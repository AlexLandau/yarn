/* @flow */

import type {Manifest} from './types.js';
import type PackageResolver from './package-resolver.js';
import type {Reporter} from './reporters/index.js';
import Config from './config.js';
import type {ReporterSetSpinner} from './reporters/types.js';
import executeLifecycleScript from './util/execute-lifecycle-script.js';
import * as crypto from './util/crypto.js';
import * as fsUtil from './util/fs.js';
import {getPlatformSpecificPackageFilename} from './util/package-name-utils.js';
import {packWithIgnoreAndHeaders} from './cli/commands/pack.js';

const fs = require('fs');
const invariant = require('invariant');
const path = require('path');

const INSTALL_STAGES = ['preinstall', 'install', 'postinstall'];

export type InstallArtifacts = {
  [pattern: string]: Array<string>,
};

export default class PackageInstallScripts {
  constructor(config: Config, resolver: PackageResolver, force: boolean) {
    this.installed = 0;
    this.resolver = resolver;
    this.reporter = config.reporter;
    this.config = config;
    this.force = force;
    this.artifacts = {};
  }

  needsPermission: boolean;
  resolver: PackageResolver;
  reporter: Reporter;
  installed: number;
  config: Config;
  force: boolean;
  artifacts: InstallArtifacts;

  setForce(force: boolean) {
    this.force = force;
  }

  setArtifacts(artifacts: InstallArtifacts) {
    this.artifacts = artifacts;
  }

  getArtifacts(): InstallArtifacts {
    return this.artifacts;
  }

  getInstallCommands(pkg: Manifest): Array<[string, string]> {
    const scripts = pkg.scripts;
    if (scripts) {
      const cmds = [];
      for (const stage of INSTALL_STAGES) {
        const cmd = scripts[stage];
        if (cmd) {
          cmds.push([stage, cmd]);
        }
      }
      return cmds;
    } else {
      return [];
    }
  }

  async walk(loc: string): Promise<Map<string, number>> {
    const files = await fsUtil.walk(loc, null, new Set(this.config.registryFolders));
    const mtimes = new Map();
    for (const file of files) {
      mtimes.set(file.relative, file.mtime);
    }
    return mtimes;
  }

  async saveBuildArtifacts(
    loc: string,
    pkg: Manifest,
    beforeFiles: Map<string, number>,
    spinner: ReporterSetSpinner,
  ): Promise<void> {
    const afterFiles = await this.walk(loc);

    // work out what files have been created/modified
    const buildArtifacts = [];
    for (const [file, mtime] of afterFiles) {
      if (!beforeFiles.has(file) || beforeFiles.get(file) !== mtime) {
        buildArtifacts.push(file);
      }
    }

    if (!buildArtifacts.length) {
      // nothing else to do here since we have no build artifacts
      return;
    }

    // set build artifacts
    const ref = pkg._reference;
    invariant(ref, 'expected reference');
    this.artifacts[`${pkg.name}@${pkg.version}`] = buildArtifacts;
  }

  async install(cmds: Array<[string, string]>, pkg: Manifest, spinner: ReporterSetSpinner): Promise<void> {
    const ref = pkg._reference;
    invariant(ref, 'expected reference');
    const locs = ref.locations;

    let updateProgress;

    if (cmds.length > 0) {
      updateProgress = data => {
        const dataStr = data
          .toString() // turn buffer into string
          .trim(); // trim whitespace

        invariant(spinner && spinner.tick, 'We should have spinner and its ticker here');
        if (dataStr) {
          spinner.tick(
            dataStr
              // Only get the last line
              .substr(dataStr.lastIndexOf('\n') + 1)
              // change tabs to spaces as they can interfere with the console
              .replace(/\t/g, ' '),
          );
        }
      };
    }

    try {
      for (const [stage, cmd] of cmds) {
        await Promise.all(
          locs.map(async loc => {
            const {stdout} = await executeLifecycleScript({
              stage,
              config: this.config,
              cwd: loc,
              cmd,
              isInteractive: false,
              updateProgress,
            });
            this.reporter.verbose(stdout);
          }),
        );
      }
    } catch (err) {
      err.message = `${locs.join(', ')}: ${err.message}`;

      invariant(ref, 'expected reference');

      if (ref.optional) {
        ref.ignore = true;
        ref.incompatible = true;
        this.reporter.warn(this.reporter.lang('optionalModuleScriptFail', err.message));
        this.reporter.info(this.reporter.lang('optionalModuleFail'));

        // Cleanup node_modules
        try {
          await Promise.all(
            locs.map(async loc => {
              await fsUtil.unlink(loc);
            }),
          );
        } catch (e) {
          this.reporter.error(this.reporter.lang('optionalModuleCleanupFail', e.message));
        }
      } else {
        throw err;
      }
    }
  }

  packageCanBeInstalled(pkg: Manifest): boolean {
    const cmds = this.getInstallCommands(pkg);
    if (!cmds.length) {
      return false;
    }
    if (this.config.packBuiltPackages && pkg.prebuiltVariants) {
      for (const variant in pkg.prebuiltVariants) {
        if (pkg._remote && pkg._remote.reference && pkg._remote.reference.includes(variant)) {
          return false;
        }
      }
    }
    const ref = pkg._reference;
    invariant(ref, 'Missing package reference');
    if (!ref.fresh && !this.force) {
      // this package hasn't been touched
      return false;
    }

    // Don't run lifecycle scripts for hoisted packages
    if (!ref.locations.length) {
      return false;
    }

    // we haven't actually written this module out
    if (ref.ignore) {
      return false;
    }
    return true;
  }

  async runCommand(spinner: ReporterSetSpinner, pkg: Manifest): Promise<void> {
    const cmds = this.getInstallCommands(pkg);
    spinner.setPrefix(++this.installed, pkg.name);
    await this.install(cmds, pkg, spinner);
  }

  // detect if there is a circularDependency in the dependency tree
  detectCircularDependencies(root: Manifest, seenManifests: Set<Manifest>, pkg: Manifest): boolean {
    const ref = pkg._reference;
    invariant(ref, 'expected reference');

    const deps = ref.dependencies;
    for (const dep of deps) {
      const pkgDep = this.resolver.getStrictResolvedPattern(dep);
      if (seenManifests.has(pkgDep)) {
        // there is a cycle but not with the root
        continue;
      }
      seenManifests.add(pkgDep);
      // found a dependency pointing to root
      if (pkgDep == root) {
        return true;
      }
      if (this.detectCircularDependencies(root, seenManifests, pkgDep)) {
        return true;
      }
    }
    return false;
  }

  // Okay, I think we can do better if we apply both the following lines of reasoning:
  // 1) Consider all our dependencies as being in one of three categories:
  //    a) Already installed dependencies
  //    b) Dependencies we've already seen in the chain (i.e. circular dependencies)
  //    c) Dependencies we haven't seen and that haven't been installed
  // 2) If all dependencies are in category A, install this package.
  // 3) If all dependencies are in categories A or B, install this package with some regrets.
  // 4) If we have any dependencies in category C, recurse on that package instead.
  // That translates into looking at individual packages as follows:
  // 1) If we're looking at a package that hasn't been seen or installed, recurse on that.
  // 2) Otherwise, if we don't see any packages in category C, return this package. Maybe try to notice
  //    if we saw anything in category B.

  // Take 2, with new categories:
  // 1) Our dependencies may now be in additional categories "beingInstalled" and "blocked". If any
  //    of our dependencies are in this category, we ourselves become blocked.
  findInstallablePackage2(startingPkg: Manifest, beingInstalled: Set<Manifest>, blocked: Set<Manifest>, installed: Set<Manifest>, seenManifests: Set<Manifest>): ?Manifest {
    const ref = startingPkg._reference;
    invariant(ref, 'expected reference');
    const deps = ref.dependencies;

    seenManifests.add(startingPkg);

    let dependenciesFulfilled = true;
    console.log("Number of deps: ", deps.length);
    for (const dep of deps) {
      const pkgDep = this.resolver.getStrictResolvedPattern(dep);
      if (beingInstalled.has(pkgDep) || blocked.has(pkgDep)) {
        console.log("Blocked on dependency ", dep);
        blocked.add(startingPkg);
        return null;
      }
      if (!installed.has(pkgDep)) {
        console.log("Unfulfilled dependency of ", startingPkg.name, startingPkg.version, " is ", dep);
        dependenciesFulfilled = false;
        // break;
        if (seenManifests.has(pkgDep)) {
          // there is a cycle here...
          return pkgDep;
        }

        console.log("Recursing");
        return this.findInstallablePackage2(pkgDep, beingInstalled, blocked, installed, seenManifests);
      }
    }

    if (!dependenciesFulfilled) {
      throw new Error("Huh?");
    }

    console.log("Returning the starting package ", startingPkg.name, startingPkg.version);
    return startingPkg;
  }

  // find the next package to be installed
  findInstallablePackage(workQueue: Set<Manifest>, beingInstalled: Set<Manifest>, blocked: Set<Manifest>, installed: Set<Manifest>): ?Manifest {
    console.log("Running findInstallablePackage, workQueue has length: ", workQueue.size);
    console.log("Installed: ", installed.size, "Installing: ", beingInstalled.size, "Blocked: ", blocked.size);

    for (const pkg of workQueue) {
      if (!blocked.has(pkg)) {
        console.log("Examining ", pkg.name, pkg.version);
        const pkgToInstall = this.findInstallablePackage2(pkg, beingInstalled, blocked, installed, new Set());
        if (pkgToInstall == null) {
          console.log("Marking as blocked ", pkg.name, pkg.version);
          blocked.add(pkg);
        } else {
          console.log("Returning ", pkgToInstall.name, pkgToInstall.version);
          return pkgToInstall;
        }
      }
    }
    return null;
  }

  async worker(
    spinner: ReporterSetSpinner,
    workQueue: Set<Manifest>,
    beingInstalled: Set<Manifest>,
    blocked: Set<Manifest>,
    installed: Set<Manifest>,
    waitQueue: Set<() => void>,
  ): Promise<void> {
    while (workQueue.size > 0) {
      // find a installable package
      const pkg = this.findInstallablePackage(workQueue, beingInstalled, blocked, installed);

      // can't find a package to install, register into waitQueue
      if (pkg == null) {
        spinner.clear();
        await new Promise(resolve => waitQueue.add(resolve));
        continue;
      }

      // found a package to install
      workQueue.delete(pkg);
      if (this.packageCanBeInstalled(pkg)) {
        beingInstalled.add(pkg);
        await this.runCommand(spinner, pkg);
        beingInstalled.delete(pkg);
        blocked.clear();
      }
      installed.add(pkg);
      for (const workerResolve of waitQueue) {
        workerResolve();
      }
      waitQueue.clear();
    }
  }

  async init(seedPatterns: Array<string>): Promise<void> {
    const workQueue = new Set();
    const beingInstalled = new Set();
    const blocked = new Set();
    const installed = new Set();
    const pkgs = this.resolver.getTopologicalManifests(seedPatterns);
    let installablePkgs = 0;
    // A map to keep track of what files exist before installation
    const beforeFilesMap = new Map();
    for (const pkg of pkgs) {
      if (this.packageCanBeInstalled(pkg)) {
        const ref = pkg._reference;
        invariant(ref, 'expected reference');
        await Promise.all(
          ref.locations.map(async loc => {
            beforeFilesMap.set(loc, await this.walk(loc));
            installablePkgs += 1;
          }),
        );
      }
      workQueue.add(pkg);
    }

    const set = this.reporter.activitySet(installablePkgs, Math.min(installablePkgs, this.config.childConcurrency));

    // waitQueue acts like a semaphore to allow workers to register to be notified
    // when there are more work added to the work queue
    const waitQueue = new Set();
    await Promise.all(set.spinners.map(spinner => this.worker(spinner, workQueue, beingInstalled, blocked, installed, waitQueue)));
    // generate built package as prebuilt one for offline mirror
    const offlineMirrorPath = this.config.getOfflineMirrorPath();
    if (this.config.packBuiltPackages && offlineMirrorPath) {
      for (const pkg of pkgs) {
        if (this.packageCanBeInstalled(pkg)) {
          let prebuiltPath = path.join(offlineMirrorPath, 'prebuilt');
          await fsUtil.mkdirp(prebuiltPath);
          const prebuiltFilename = getPlatformSpecificPackageFilename(pkg);
          prebuiltPath = path.join(prebuiltPath, prebuiltFilename + '.tgz');
          const ref = pkg._reference;
          invariant(ref, 'expected reference');
          const builtPackagePaths = ref.locations;

          await Promise.all(
            builtPackagePaths.map(async builtPackagePath => {
              // don't use pack command, we want to avoid the file filters logic
              const stream = await packWithIgnoreAndHeaders(builtPackagePath);

              const hash = await new Promise((resolve, reject) => {
                const validateStream = new crypto.HashStream();
                stream
                  .pipe(validateStream)
                  .pipe(fs.createWriteStream(prebuiltPath))
                  .on('error', reject)
                  .on('close', () => resolve(validateStream.getHash()));
              });
              pkg.prebuiltVariants = pkg.prebuiltVariants || {};
              pkg.prebuiltVariants[prebuiltFilename] = hash;
            }),
          );
        }
      }
    } else {
      // cache all build artifacts
      for (const pkg of pkgs) {
        if (this.packageCanBeInstalled(pkg)) {
          const ref = pkg._reference;
          invariant(ref, 'expected reference');
          const beforeFiles = ref.locations.map(loc => beforeFilesMap.get(loc));
          await Promise.all(
            beforeFiles.map(async (b, index) => {
              invariant(b, 'files before installation should always be recorded');
              await this.saveBuildArtifacts(ref.locations[index], pkg, b, set.spinners[0]);
            }),
          );
        }
      }
    }

    set.end();
  }
}

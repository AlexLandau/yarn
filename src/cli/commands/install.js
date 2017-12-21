/* @flow */

import type {InstallationMethod} from '../../util/yarn-version.js';
import type {Reporter} from '../../reporters/index.js';
import type {ReporterSelectOption} from '../../reporters/types.js';
import type {Manifest, DependencyRequestPatterns} from '../../types.js';
import type Config from '../../config.js';
import type {RegistryNames} from '../../registries/index.js';
import type {LockfileObject} from '../../lockfile';
import normalizeManifest from '../../util/normalize-manifest/index.js';
import {MessageError} from '../../errors.js';
import InstallationIntegrityChecker from '../../integrity-checker.js';
import Lockfile from '../../lockfile';
import {stringify as lockStringify} from '../../lockfile';
import * as fetcher from '../../package-fetcher.js';
import PackageInstallScripts from '../../package-install-scripts.js';
import * as compatibility from '../../package-compatibility.js';
import PackageResolver from '../../package-resolver.js';
import PackageLinker from '../../package-linker.js';
import {registries} from '../../registries/index.js';
import {getExoticResolver} from '../../resolvers/index.js';
import {clean} from './autoclean.js';
import * as constants from '../../constants.js';
import {normalizePattern} from '../../util/normalize-pattern.js';
import * as fs from '../../util/fs.js';
import map from '../../util/map.js';
import {version as YARN_VERSION, getInstallationMethod} from '../../util/yarn-version.js';
import WorkspaceLayout from '../../workspace-layout.js';
import ResolutionMap from '../../resolution-map.js';
import guessName from '../../util/guess-name';
import PackageHoister from '../../package-hoister.js';
import { hash } from '../../util/crypto';

const emoji = require('node-emoji');
const invariant = require('invariant');
const path = require('path');
const semver = require('semver');
const uuid = require('uuid');

const ONE_DAY = 1000 * 60 * 60 * 24;

export type InstallCwdRequest = {
  requests: DependencyRequestPatterns,
  patterns: Array<string>,
  ignorePatterns: Array<string>,
  usedPatterns: Array<string>,
  manifest: Object,
  workspaceLayout?: WorkspaceLayout,
};

type Flags = {
  // install
  har: boolean,
  ignorePlatform: boolean,
  ignoreEngines: boolean,
  ignoreScripts: boolean,
  ignoreOptional: boolean,
  linkDuplicates: boolean,
  force: boolean,
  flat: boolean,
  lockfile: boolean,
  pureLockfile: boolean,
  frozenLockfile: boolean,
  skipIntegrityCheck: boolean,
  checkFiles: boolean,

  // add
  peer: boolean,
  dev: boolean,
  optional: boolean,
  exact: boolean,
  tilde: boolean,
  ignoreWorkspaceRootCheck: boolean,

  // outdated, update-interactive
  includeWorkspaceDeps: boolean,

  // remove, upgrade
  workspaceRootIsCwd: boolean,
};

/**
 * Try and detect the installation method for Yarn and provide a command to update it with.
 */

function getUpdateCommand(installationMethod: InstallationMethod): ?string {
  if (installationMethod === 'tar') {
    return `curl -o- -L ${constants.YARN_INSTALLER_SH} | bash`;
  }

  if (installationMethod === 'homebrew') {
    return 'brew upgrade yarn';
  }

  if (installationMethod === 'deb') {
    return 'sudo apt-get update && sudo apt-get install yarn';
  }

  if (installationMethod === 'rpm') {
    return 'sudo yum install yarn';
  }

  if (installationMethod === 'npm') {
    return 'npm install --global yarn';
  }

  if (installationMethod === 'chocolatey') {
    return 'choco upgrade yarn';
  }

  if (installationMethod === 'apk') {
    return 'apk update && apk add -u yarn';
  }

  return null;
}

function getUpdateInstaller(installationMethod: InstallationMethod): ?string {
  // Windows
  if (installationMethod === 'msi') {
    return constants.YARN_INSTALLER_MSI;
  }

  return null;
}

function normalizeFlags(config: Config, rawFlags: Object): Flags {
  const flags = {
    // install
    har: !!rawFlags.har,
    ignorePlatform: !!rawFlags.ignorePlatform,
    ignoreEngines: !!rawFlags.ignoreEngines,
    ignoreScripts: !!rawFlags.ignoreScripts,
    ignoreOptional: !!rawFlags.ignoreOptional,
    force: !!rawFlags.force,
    flat: !!rawFlags.flat,
    lockfile: rawFlags.lockfile !== false,
    pureLockfile: !!rawFlags.pureLockfile,
    updateChecksums: !!rawFlags.updateChecksums,
    skipIntegrityCheck: !!rawFlags.skipIntegrityCheck,
    frozenLockfile: !!rawFlags.frozenLockfile,
    linkDuplicates: !!rawFlags.linkDuplicates,
    checkFiles: !!rawFlags.checkFiles,

    // add
    peer: !!rawFlags.peer,
    dev: !!rawFlags.dev,
    optional: !!rawFlags.optional,
    exact: !!rawFlags.exact,
    tilde: !!rawFlags.tilde,
    ignoreWorkspaceRootCheck: !!rawFlags.ignoreWorkspaceRootCheck,

    // outdated, update-interactive
    includeWorkspaceDeps: !!rawFlags.includeWorkspaceDeps,

    // remove, update
    workspaceRootIsCwd: rawFlags.workspaceRootIsCwd !== false,
  };

  if (config.getOption('ignore-scripts')) {
    flags.ignoreScripts = true;
  }

  if (config.getOption('ignore-platform')) {
    flags.ignorePlatform = true;
  }

  if (config.getOption('ignore-engines')) {
    flags.ignoreEngines = true;
  }

  if (config.getOption('ignore-optional')) {
    flags.ignoreOptional = true;
  }

  if (config.getOption('force')) {
    flags.force = true;
  }

  return flags;
}

export class Install {
  constructor(flags: Object, config: Config, reporter: Reporter, lockfile: Lockfile) {
    this.rootManifestRegistries = [];
    this.rootPatternsToOrigin = map();
    this.lockfile = lockfile;
    this.reporter = reporter;
    this.config = config;
    this.flags = normalizeFlags(config, flags);
    this.resolutions = map(); // Legacy resolutions field used for flat install mode
    this.resolutionMap = new ResolutionMap(config); // Selective resolutions for nested dependencies
    this.resolver = new PackageResolver(config, lockfile, this.resolutionMap);
    this.integrityChecker = new InstallationIntegrityChecker(config);
    this.linker = new PackageLinker(config, this.resolver);
    this.scripts = new PackageInstallScripts(config, this.resolver, this.flags.force);
  }

  flags: Flags;
  rootManifestRegistries: Array<RegistryNames>;
  registries: Array<RegistryNames>;
  lockfile: Lockfile;
  resolutions: {[packageName: string]: string};
  config: Config;
  reporter: Reporter;
  resolver: PackageResolver;
  scripts: PackageInstallScripts;
  linker: PackageLinker;
  rootPatternsToOrigin: {[pattern: string]: string};
  integrityChecker: InstallationIntegrityChecker;
  resolutionMap: ResolutionMap;



  async getDependenciesFromManifest(projectManifestJson) {
    const patterns = [];
    const deps: DependencyRequestPatterns = [];
    const ignorePatterns = [];
    const usedPatterns = [];

    const cwd =
    this.flags.includeWorkspaceDeps || this.flags.workspaceRootIsCwd ? this.config.lockfileFolder : this.config.cwd;

    for (const registry of Object.keys(registries)) {
      const {filename} = registries[registry];
      const loc = path.join(cwd, filename);
      if (!await fs.exists(loc)) {
        continue;
      }

      const pushDeps = (depType, manifest: Object, {hint, optional}, isUsed) => {
        // We only take unused dependencies into consideration to get deterministic hoisting.
        // Since flat mode doesn't care about hoisting and everything is top level and specified then we can safely
        // leave these out.
        if (this.flags.flat && !isUsed) {
          return;
        }
        const depMap = manifest[depType];
        for (const name in depMap) {
          let pattern = name;
          if (!this.lockfile.getLocked(pattern)) {
            // when we use --save we save the dependency to the lockfile with just the name rather than the
            // version combo
            pattern += '@' + depMap[name];
          }

          // normalization made sure packages are mentioned only once
          if (isUsed) {
            usedPatterns.push(pattern);
          } else {
            ignorePatterns.push(pattern);
          }

          this.rootPatternsToOrigin[pattern] = depType;
          patterns.push(pattern);
          deps.push({pattern, registry, hint, optional, workspaceName: manifest.name, workspaceLoc: manifest._loc});
        }
      };

      pushDeps('dependencies', projectManifestJson, {hint: null, optional: false}, true);
      pushDeps('devDependencies', projectManifestJson, {hint: 'dev', optional: false}, !this.config.production);
      pushDeps('optionalDependencies', projectManifestJson, {hint: 'optional', optional: true}, true);

      break;
    }
    return {patterns, deps};
  }

  /**
   * Create a list of dependency requests from the current directories manifests.
   */

  async fetchRequestFromCwd(
    excludePatterns?: Array<string> = [],
    ignoreUnusedPatterns?: boolean = false,
  ): Promise<InstallCwdRequest> {
    const patterns = [];
    const deps: DependencyRequestPatterns = [];
    let resolutionDeps: DependencyRequestPatterns = [];
    const manifest = {};

    const ignorePatterns = [];
    const usedPatterns = [];
    let workspaceLayout;

    // some commands should always run in the context of the entire workspace
    const cwd =
      this.flags.includeWorkspaceDeps || this.flags.workspaceRootIsCwd ? this.config.lockfileFolder : this.config.cwd;

    // non-workspaces are always root, otherwise check for workspace root
    const cwdIsRoot = !this.config.workspaceRootFolder || this.config.lockfileFolder === cwd;

    // exclude package names that are in install args
    const excludeNames = [];
    for (const pattern of excludePatterns) {
      if (getExoticResolver(pattern)) {
        excludeNames.push(guessName(pattern));
      } else {
        // extract the name
        const parts = normalizePattern(pattern);
        excludeNames.push(parts.name);
      }
    }

    const stripExcluded = (manifest: Manifest) => {
      for (const exclude of excludeNames) {
        if (manifest.dependencies && manifest.dependencies[exclude]) {
          delete manifest.dependencies[exclude];
        }
        if (manifest.devDependencies && manifest.devDependencies[exclude]) {
          delete manifest.devDependencies[exclude];
        }
        if (manifest.optionalDependencies && manifest.optionalDependencies[exclude]) {
          delete manifest.optionalDependencies[exclude];
        }
      }
    };

    for (const registry of Object.keys(registries)) {
      const {filename} = registries[registry];
      const loc = path.join(cwd, filename);
      if (!await fs.exists(loc)) {
        continue;
      }

      this.rootManifestRegistries.push(registry);

      const projectManifestJson = await this.config.readJson(loc);
      await normalizeManifest(projectManifestJson, cwd, this.config, cwdIsRoot);

      Object.assign(this.resolutions, projectManifestJson.resolutions);
      Object.assign(manifest, projectManifestJson);

      this.resolutionMap.init(this.resolutions);
      for (const packageName of Object.keys(this.resolutionMap.resolutionsByPackage)) {
        for (const {pattern} of this.resolutionMap.resolutionsByPackage[packageName]) {
          resolutionDeps = [...resolutionDeps, {registry, pattern, optional: false, hint: 'resolution'}];
        }
      }

      const pushDeps = (depType, manifest: Object, {hint, optional}, isUsed) => {
        if (ignoreUnusedPatterns && !isUsed) {
          return;
        }
        // We only take unused dependencies into consideration to get deterministic hoisting.
        // Since flat mode doesn't care about hoisting and everything is top level and specified then we can safely
        // leave these out.
        if (this.flags.flat && !isUsed) {
          return;
        }
        const depMap = manifest[depType];
        for (const name in depMap) {
          if (excludeNames.indexOf(name) >= 0) {
            continue;
          }

          let pattern = name;
          if (!this.lockfile.getLocked(pattern)) {
            // when we use --save we save the dependency to the lockfile with just the name rather than the
            // version combo
            pattern += '@' + depMap[name];
          }

          // normalization made sure packages are mentioned only once
          if (isUsed) {
            usedPatterns.push(pattern);
          } else {
            ignorePatterns.push(pattern);
          }

          this.rootPatternsToOrigin[pattern] = depType;
          patterns.push(pattern);
          deps.push({pattern, registry, hint, optional, workspaceName: manifest.name, workspaceLoc: manifest._loc});
        }
      };

      pushDeps('dependencies', projectManifestJson, {hint: null, optional: false}, true);
      pushDeps('devDependencies', projectManifestJson, {hint: 'dev', optional: false}, !this.config.production);
      pushDeps('optionalDependencies', projectManifestJson, {hint: 'optional', optional: true}, true);

      // Looks relevant
      // (fixing this is probably going to suck)
      if (this.config.workspaceRootFolder) {
        console.log("There is a workspaceRootFolder");
        const workspaceLoc = cwdIsRoot ? loc : path.join(this.config.lockfileFolder, filename);
        const workspacesRoot = path.dirname(workspaceLoc);

        let workspaceManifestJson = projectManifestJson;
        if (!cwdIsRoot) {
          // the manifest we read before was a child workspace, so get the root
          workspaceManifestJson = await this.config.readJson(workspaceLoc);
          await normalizeManifest(workspaceManifestJson, workspacesRoot, this.config, true);
        }

        // TODO: This does unnecessary loads of the READMEs... *facepalm*
        const workspaces = await this.config.resolveWorkspaces(workspacesRoot, workspaceManifestJson);
        // console.log("workspaces: ", workspaces);
        workspaceLayout = new WorkspaceLayout(workspaces, this.config);
        console.log("workspaceLayout: ", workspaceLayout);
        // This is pretty important!

        // add virtual manifest that depends on all workspaces, this way package hoisters and resolvers will work fine
        // TODO: This might NOT be what we want here...
        const workspaceDependencies = {...workspaceManifestJson.dependencies};
        console.log("workspaceDependencies: ", workspaceDependencies);
        for (const workspaceName of Object.keys(workspaces)) {
          const workspaceManifest = workspaces[workspaceName].manifest;
          workspaceDependencies[workspaceName] = workspaceManifest.version;

          // include dependencies from all workspaces
          if (this.flags.includeWorkspaceDeps) {
            pushDeps('dependencies', workspaceManifest, {hint: null, optional: false}, true);
            pushDeps('devDependencies', workspaceManifest, {hint: 'dev', optional: false}, !this.config.production);
            pushDeps('optionalDependencies', workspaceManifest, {hint: 'optional', optional: true}, true);
          }
        }
        // For hack week, don't include the fake project manifest
        // const virtualDependencyManifest: Manifest = {
        //   _uid: '',
        //   name: `workspace-aggregator-${uuid.v4()}`,
        //   version: '1.0.0',
        //   _registry: 'npm',
        //   _loc: workspacesRoot,
        //   dependencies: workspaceDependencies,
        //   devDependencies: {...workspaceManifestJson.devDependencies},
        //   optionalDependencies: {...workspaceManifestJson.optionalDependencies},
        // };
        // workspaceLayout.virtualManifestName = virtualDependencyManifest.name;
        // const virtualDep = {};
        // virtualDep[virtualDependencyManifest.name] = virtualDependencyManifest.version;
        // workspaces[virtualDependencyManifest.name] = {loc: workspacesRoot, manifest: virtualDependencyManifest};

        // // ensure dependencies that should be excluded are stripped from the correct manifest
        // stripExcluded(cwdIsRoot ? virtualDependencyManifest : workspaces[projectManifestJson.name].manifest);

        // pushDeps('workspaces', {workspaces: virtualDep}, {hint: 'workspaces', optional: false}, true);
      }

      break;
    }

    // inherit root flat flag
    if (manifest.flat) {
      this.flags.flat = true;
    }

    console.log("Patterns: ", patterns);
    console.log("Deps: ", deps);
    console.log("resolutionDeps: ", resolutionDeps);

    return {
      requests: [...resolutionDeps, ...deps],
      patterns,
      manifest,
      usedPatterns,
      ignorePatterns,
      workspaceLayout,
    };
  }

  /**
   * TODO description
   */

  prepareRequests(requests: DependencyRequestPatterns): DependencyRequestPatterns {
    return requests;
  }

  preparePatterns(patterns: Array<string>): Array<string> {
    return patterns;
  }

  async bailout(patterns: Array<string>, workspaceLayout: ?WorkspaceLayout): Promise<boolean> {
    if (this.flags.skipIntegrityCheck || this.flags.force) {
      return false;
    }
    const lockfileCache = this.lockfile.cache;
    if (!lockfileCache) {
      return false;
    }
    const lockfileClean = this.lockfile.parseResultType === 'success';
    const match = await this.integrityChecker.check(patterns, lockfileCache, this.flags, workspaceLayout);
    if (this.flags.frozenLockfile && (!lockfileClean || match.missingPatterns.length > 0)) {
      throw new MessageError(this.reporter.lang('frozenLockfileError'));
    }

    const haveLockfile = await fs.exists(path.join(this.config.lockfileFolder, constants.LOCKFILE_FILENAME));

    if (match.integrityMatches && haveLockfile && lockfileClean) {
      this.reporter.success(this.reporter.lang('upToDate'));
      return true;
    }

    if (match.integrityFileMissing && haveLockfile) {
      // Integrity file missing, force script installations
      this.scripts.setForce(true);
      return false;
    }

    if (match.hardRefreshRequired) {
      // e.g. node version doesn't match, force script installations
      this.scripts.setForce(true);
      return false;
    }

    if (!patterns.length && !match.integrityFileMissing) {
      this.reporter.success(this.reporter.lang('nothingToInstall'));
      await this.createEmptyManifestFolders();
      await this.saveLockfileAndIntegrity(patterns, workspaceLayout);
      return true;
    }

    return false;
  }

  /**
   * Produce empty folders for all used root manifests.
   */

  async createEmptyManifestFolders(): Promise<void> {
    if (this.config.modulesFolder) {
      // already created
      return;
    }

    for (const registryName of this.rootManifestRegistries) {
      const {folder} = this.config.registries[registryName];
      await fs.mkdirp(path.join(this.config.lockfileFolder, folder));
    }
  }

  /**
   * TODO description
   */

  markIgnored(patterns: Array<string>) {
    for (const pattern of patterns) {
      const manifest = this.resolver.getStrictResolvedPattern(pattern);
      const ref = manifest._reference;
      invariant(ref, 'expected package reference');

      // just mark the package as ignored. if the package is used by a required package, the hoister
      // will take care of that.
      ref.ignore = true;
    }
  }

  /**
   * TODO description
   */

  async init(): Promise<Array<string>> {
    console.log("Entering Install.init()");
    this.checkUpdate();

    // warn if we have a shrinkwrap
    if (await fs.exists(path.join(this.config.lockfileFolder, 'npm-shrinkwrap.json'))) {
      this.reporter.warn(this.reporter.lang('shrinkwrapWarning'));
    }

    let flattenedTopLevelPatterns: Array<string> = [];
    const steps: Array<(curr: number, total: number) => Promise<{bailout: boolean} | void>> = [];
    // TODO: We're going to need to fix this to work differently (probably)
    // We'll need some way to see... ___
    const {
      requests: depRequests,
      patterns: rawPatterns,
      ignorePatterns,
      workspaceLayout,
      manifest,
    } = await this.fetchRequestFromCwd();
    let topLevelPatterns: Array<string> = [];

    const artifacts = await this.integrityChecker.getArtifacts();
    // console.log("Artifacts: ", artifacts);
    if (artifacts) {
      this.linker.setArtifacts(artifacts);
      this.scripts.setArtifacts(artifacts);
    }

    if (!this.flags.ignoreEngines && typeof manifest.engines === 'object') {
      console.log("Adding a checkingManifest step");
      steps.push(async (curr: number, total: number) => {
        this.reporter.step(curr, total, this.reporter.lang('checkingManifest'), emoji.get('mag'));
        await compatibility.checkOne({_reference: {}, ...manifest}, this.config, this.flags.ignoreEngines);
      });
    }

    // At this point, we have the workspaceLayout, so...
    if (workspaceLayout != null) {
      console.log("Doing alandau's hack week stuff instead of a normal yarn workspaces install");

      // TODO: As best as possible, ignore the following variables...
      // depRequests
      // rawPatterns
      // ignorePatterns
      // manifest
      console.log("depRequests: ", depRequests); // parsed dependencies for the root project, plus the fake workspace project
      // console.log("rawPatterns: ", rawPatterns); // raw dependencies for the root project, plus the fake workspace project
      // console.log("ignorePatterns: ", ignorePatterns); // This is empty for us
      // console.log("manifest: ", manifest); // This is the package.json for the root project


      // console.log("workspaceLayout.workspaces: ", workspaceLayout.workspaces); // loc and manifest for everything... plus the fake stuff
      // Can we map to the requests for each project?
      const depRequestsByWorkspace = {};
      const patternsByWorkspace = {};
      const allDepRequests = [];
      allDepRequests.push(...depRequests);
      for (const workspaceName in workspaceLayout.workspaces) {
        console.log("Dependencies for " + workspaceName + ":");
        console.log("  deps: ", workspaceLayout.workspaces[workspaceName].manifest.dependencies);
        console.log("  devDeps: ", workspaceLayout.workspaces[workspaceName].manifest.devDependencies);
        console.log("  peerDeps: ", workspaceLayout.workspaces[workspaceName].manifest.peerDependencies);
        const foo /*depRequestsInWorkspace*/ = await this.getDependenciesFromManifest(workspaceLayout.workspaces[workspaceName].manifest);
        const depRequestsInWorkspace = foo.deps;
        const patternsInWorkspace = foo.patterns;
        console.log("Parsed dependencies: ", depRequestsInWorkspace);
        depRequestsByWorkspace[workspaceName] = depRequestsInWorkspace;
        patternsByWorkspace[workspaceName] = patternsInWorkspace;
        allDepRequests.push(...depRequestsInWorkspace);
      }
      console.log("depRequests: ", depRequests); // parsed dependencies for the root project, plus the fake workspace project

      // First step: What are all our workspace projects? (And presumably we also have the top-level thing to worry about)
      steps.push(async (curr: number, total: number) => {
        this.reporter.step(curr, total, "alandauResolvePackagesStep");
        // TODO: Some deduplication here might be appropriate?
        await this.resolver.init(this.prepareRequests(allDepRequests), {
          isFlat: this.flags.flat,
          isFrozen: this.flags.frozenLockfile,
          workspaceLayout,
        });
        // Fine for hack week
        return {bailout: false};
      });

      // Now we fetch, I guess?
      steps.push(async (curr: number, total: number) => {
        this.markIgnored(ignorePatterns);
        this.reporter.step(curr, total, "alandauFetchPackagesStep");
        console.log("About to get the manifests from this.resolver");
        const manifests: Array<Manifest> = await fetcher.fetch(this.resolver.getManifests(), this.config);
        this.resolver.updateManifests(manifests);
        await compatibility.check(this.resolver.getManifests(), this.config, this.flags.ignoreEngines);
      });

      // And now we do the actual file system manipulation stuff
      steps.push(async (curr: number, total: number) => {
        // remove integrity hash to make this operation atomic
        await this.integrityChecker.removeIntegrityFile();
        this.reporter.step(curr, total, "alandauLinkingDependencies");
        // This part is probably going to have to be overhauled
        console.log("rawPatterns: ", rawPatterns);
        topLevelPatterns = this.preparePatterns(rawPatterns);
        console.log("topLevelPatterns: ", topLevelPatterns);
        flattenedTopLevelPatterns = await this.flatten(topLevelPatterns);
        // console.log("flattenedTopLevelPatterns: " + flattenedTopLevelPatterns);
        console.log("flattenedTopLevelPatterns: ", flattenedTopLevelPatterns);
        // Now is where the linker would run...

        console.log("So what does the 'flat hoisted tree' look like for flattenedTopLevelPatterns?");
        // So why does this know stuff already?
        // It knows the Resolver, is that the problem?

        // const flatHoistedTree: HoistManifestTuples = this.linker.getFlatHoistedTree(flattenedTopLevelPatterns, {ignoreOptional: this.flags.ignoreOptional});
        const rootHoister = new PackageHoister(this.config, this.resolver, {ignoreOptional: this.flags.ignoreOptional});
        rootHoister.seed(flattenedTopLevelPatterns);
        const rootFlatHoistedTree: HoistManifestTuples =  rootHoister.init();

        // console.log("flatHoistedTree: ", flatHoistedTree);
        console.log("flatHoistedTree:");
        for (const item of rootFlatHoistedTree) {
          const location: String = item[0];
          const hoistManifest: HoistManifest = item[1];
          console.log(location, ": ", hoistManifest.originalKey, " -> ", hoistManifest.key);
          // console.log(item);
        }
        const interWorkspaceDeps = {};

        const workspaceFlatHoistedTrees = {};
        workspaceFlatHoistedTrees[""] = rootFlatHoistedTree;
        for (const workspaceName in workspaceLayout.workspaces) {
          interWorkspaceDeps[workspaceName] = []; // TODO: Maybe this should be a Set instead
          // TODO: Probably modify the config to get the destination path right?
          const workspaceHoister = new PackageHoister(this.config, this.resolver, {ignoreOptional: this.flags.ignoreOptional});
          // TODO: Get a valid input here
          const wsRawPatterns = patternsByWorkspace[workspaceName];
          const wsTopLevelPatterns = this.preparePatterns(wsRawPatterns);
          // console.log("wsTopLevelPatterns: ", wsTopLevelPatterns);
          const wsFlattenedTopLevelPatternsTmp = await this.flatten(wsTopLevelPatterns);
          const depsToRemove = [];
          for (const dep of wsFlattenedTopLevelPatternsTmp) {
            const atIndex = dep.lastIndexOf('@');
            const depNameWithoutVersion = dep.substring(0, atIndex);
            // console.log(depNameWithoutVersion);
            if (depNameWithoutVersion in workspaceLayout.workspaces) {
              // console.log("  (is a workspace)");
              interWorkspaceDeps[workspaceName].push(depNameWithoutVersion);
              depsToRemove.push(dep);
            }
          }
          const wsFlattenedTopLevelPatterns = wsFlattenedTopLevelPatternsTmp.filter((value: String) => depsToRemove.indexOf(value) === -1);
          // console.log("wsFlattenedTopLevelPatterns: ", wsFlattenedTopLevelPatterns);
          workspaceHoister.seed(wsFlattenedTopLevelPatterns);
          const workspaceFlatHoistedTree: HoistManifestTuples = workspaceHoister.init();
          workspaceFlatHoistedTrees[workspaceName] = workspaceFlatHoistedTree;
        }
        const depFolderToHoistManifestsPerWorkspace = {};
        const allTopLevelDepFolders = new Set();

        for (const workspaceName in workspaceFlatHoistedTrees) { // Includes the root (""), unlike the previous loop
          const workspaceFlatHoistedTree = workspaceFlatHoistedTrees[workspaceName];
          console.log("flatHoistedTree for ", workspaceName, " has ", workspaceFlatHoistedTree.length, " entries");
          const depFolderToHoistManifests = {};
          for (const item of workspaceFlatHoistedTree) {
            const location: String = item[0];
            const hoistManifest: HoistManifest = item[1];
            // console.log(location, ": ", hoistManifest.originalKey, " -> ", hoistManifest.key);
            // console.log(item);
            const firstPart = hoistManifest.parts[0];
            if (depFolderToHoistManifests[firstPart] === undefined) {
              depFolderToHoistManifests[firstPart] = [];
              allTopLevelDepFolders.add(firstPart);
            }
            depFolderToHoistManifests[firstPart].push(hoistManifest);
          }
          // for (const topLevelDep in depFolderToHoistManifests) {
          //   console.log(topLevelDep, ": ", depFolderToHoistManifests[topLevelDep]);
          // }
          depFolderToHoistManifestsPerWorkspace[workspaceName] = depFolderToHoistManifests;
          // Let's try aggregating these into things...
        }

        console.log("Now the aggregated bits...");
        // Just checking...
        const allTopLevelDepFoldersSorted = [];
        allTopLevelDepFolders.forEach((value) => allTopLevelDepFoldersSorted.push(value));
        allTopLevelDepFoldersSorted.sort();
        const projectsUsingDepFolderType = {};
        // TODO: The other thing we'll need here is a link from the "dep folder type" to a list of HoistManifests or w/e defining
        // the sources of the stuff to copy around
        const hoistManifestsByDepFolderType = {};
        for (const topLevelDep of allTopLevelDepFoldersSorted) {
          console.log("  ", topLevelDep);
          for (const workspaceName in depFolderToHoistManifestsPerWorkspace) {
            const manifests = depFolderToHoistManifestsPerWorkspace[workspaceName][topLevelDep];
            if (manifests !== undefined) {
              // TODO: Strictly speaking, we should probably sort contents (using a canonical string comparator) before
              // toString(), but so far I'm seeing things have a consistent sorting, probably thanks to undocumented and
              // non-guaranteed behavior of other components. Good enough for hack week
              // hoistManifest.key + ":" + hoistManifest.pkg.version
              const depFolderType = manifests.map((hoistManifest: HoistManifest) => hoistManifest.key + ":" + hoistManifest.pkg.version).toString();
              console.log("    ", depFolderType, ":", workspaceName);
              if (projectsUsingDepFolderType[depFolderType] === undefined) {
                projectsUsingDepFolderType[depFolderType] = [];
              }
              projectsUsingDepFolderType[depFolderType].push(workspaceName);
              if (hoistManifestsByDepFolderType[depFolderType] === undefined) {
                hoistManifestsByDepFolderType[depFolderType] = manifests;
              }
            }
          }
        }

        console.log("Projects using dep folder type:");
        console.log(projectsUsingDepFolderType);

        console.log("The root project directory is " + workspaceLayout.config.cwd);
        const sharedModulesPath = workspaceLayout.config.cwd + "/shared_modules";
        fs.mkdirp(sharedModulesPath);
        const copyQueue = [];
        for (const depFolderType in projectsUsingDepFolderType) {
          const projectsUsingThis = projectsUsingDepFolderType[depFolderType];
          const hoistManifests = hoistManifestsByDepFolderType[depFolderType];
          if (projectsUsingThis.length > 1) {
            // Put in the shared folder, add symlinks
            console.log("Should be creating shared folder for ", projectsUsingThis.length, " projects for ", depFolderType);
            const hashMaybe = hash(depFolderType);
            console.log("  Possible hash: ", hashMaybe);
            const topLevelPath = sharedModulesPath + "/" + hashMaybe;
            fs.mkdirp(topLevelPath);
            console.log("  Original location(s) might be:");
            let topLevelBin = undefined;
            for (const hoistManifest of hoistManifests) {
              const copySrc = hoistManifest.loc;
              console.log("    ", copySrc);
              // console.log("   full hoist manifest: ", hoistManifest);
              let copyDest = topLevelPath;
              for (const part of hoistManifest.parts.slice(1)) {
                copyDest = copyDest + "/node_modules/" + part;
              }
              console.log("    copy to: ", copyDest);
              // await fs.copy(copySrc, copyDest, this.config.reporter);
              copyQueue.push({src: copySrc, dest: copyDest});

              // Look for bins from the top-level dependency only
              if (hoistManifest.parts.length === 1) { // might mean same thing as isDirectRequire?
                topLevelBin = hoistManifest.pkg.bin
              }
            }

            for (const projectName of projectsUsingThis) {
              const projectLoc = projectName === "" ? workspaceLayout.config.cwd : workspaceLayout.getWorkspaceManifest(projectName).loc;
              const depFolderName = depFolderType.slice(0, depFolderType.indexOf(":"));
              const symlinkLocation = projectLoc + "/node_modules/" + depFolderName;
              const symlinkTarget = topLevelPath;
              // TODO: Should probably relativize the targets relative to the locations
              console.log("  Add symlink: ", symlinkLocation, " to ", symlinkTarget);
              // await fs.symlink(symlinkLocation, symlinkTarget);
              copyQueue.push({src: symlinkTarget, dest: symlinkLocation, type: "symlink"})

              // Add bins if they exist
              if (topLevelBin !== undefined) {
                for (const binName in topLevelBin) {
                  const binLinkLocation = projectLoc + "/node_modules/.bin/" + binName;
                  const binTarget = symlinkTarget + "/" + topLevelBin[binName];
                  console.log(" ***** Want to link bin: from " + binLinkLocation + " to " + binTarget);
                  copyQueue.push({src: binTarget, dest: binLinkLocation, type: "symlink"});
                }
              }
            }
            // fs.copy(src, dest, reporter);
            // fs.symlink(src, dest);
          } else {
            // Put in the project folder directly
            console.log("Should be copying directly into ", projectsUsingThis[0], " for ", depFolderType);
            console.log("  Original location(s) might be:");
            const projectName = projectsUsingThis[0];
            // const projectLoc = workspaceLayout.getWorkspaceManifest(projectName).loc;
            const projectLoc = projectName === "" ? workspaceLayout.config.cwd : workspaceLayout.getWorkspaceManifest(projectName).loc;

            let topLevelBin = undefined;
            for (const hoistManifest of hoistManifests) {
              const copySrc = hoistManifest.loc;
              console.log("    ", copySrc);
              // console.log("   full hoist manifest: ", hoistManifest);
              let copyDest = projectLoc;
              for (const part of hoistManifest.parts) {
                copyDest = copyDest + "/node_modules/" + part;
              }
              console.log("    copy to: ", copyDest);
              // await fs.copy(copySrc, copyDest, this.config.reporter);
              copyQueue.push({src: copySrc, dest: copyDest});

              // Look for bins from the top-level dependency only
              if (hoistManifest.parts.length === 1) { // might mean same thing as isDirectRequire?
                topLevelBin = hoistManifest.pkg.bin
              }
            }

            // Add bins if they exist
            if (topLevelBin !== undefined) {
              for (const binName in topLevelBin) {
                const binLinkLocation = projectLoc + "/node_modules/.bin/" + binName;
                const binTarget = projectLoc + "/node_modules/" + hoistManifests[0].parts[0] + "/" + topLevelBin[binName];
                console.log(" ***** Want to link bin: from " + binLinkLocation + " to " + binTarget);
                copyQueue.push({src: binTarget, dest: binLinkLocation, type: "symlink"});
              }
            }
          }
        }
        await fs.copyBulk(copyQueue, this.config.reporter);
        // TODO: And here we can start turning those things on their head to figure out a small number of shared dependencies
        // to use per project

        // So what would it look like to have ___?
        /*

        Map from top-level folder (dependency name, or @group/name) to contents (_ and versions and all that)

        Then we compare these maps across projects

        */

        // await this.linker.init(flattenedTopLevelPatterns, workspaceLayout, {
        //   linkDuplicates: this.flags.linkDuplicates,
        //   ignoreOptional: this.flags.ignoreOptional,
        // });
      });

    } else {
      console.log("Adding a resolvingPackages step");
      steps.push(async (curr: number, total: number) => {
        this.reporter.step(curr, total, this.reporter.lang('resolvingPackages'), emoji.get('mag'));
        this.resolutionMap.setTopLevelPatterns(rawPatterns);
        await this.resolver.init(this.prepareRequests(depRequests), {
          isFlat: this.flags.flat,
          isFrozen: this.flags.frozenLockfile,
          workspaceLayout,
        });
        console.log("rawPatterns: " + rawPatterns);
        topLevelPatterns = this.preparePatterns(rawPatterns);
        console.log("topLevelPatterns: " + topLevelPatterns);
        flattenedTopLevelPatterns = await this.flatten(topLevelPatterns);
        console.log("flattenedTopLevelPatterns: " + flattenedTopLevelPatterns);
        return {bailout: await this.bailout(topLevelPatterns, workspaceLayout)};
      });

      console.log("Adding a fetchingPackages step");
      steps.push(async (curr: number, total: number) => {
        this.markIgnored(ignorePatterns);
        this.reporter.step(curr, total, this.reporter.lang('fetchingPackages'), emoji.get('truck'));
        console.log("About to get the manifests from this.resolver");
        const manifests: Array<Manifest> = await fetcher.fetch(this.resolver.getManifests(), this.config);
        this.resolver.updateManifests(manifests);
        await compatibility.check(this.resolver.getManifests(), this.config, this.flags.ignoreEngines);
      });

      console.log("Adding a linkingDependencies step");
      steps.push(async (curr: number, total: number) => {
        // remove integrity hash to make this operation atomic
        await this.integrityChecker.removeIntegrityFile();
        this.reporter.step(curr, total, this.reporter.lang('linkingDependencies'), emoji.get('link'));
        await this.linker.init(flattenedTopLevelPatterns, workspaceLayout, {
          linkDuplicates: this.flags.linkDuplicates,
          ignoreOptional: this.flags.ignoreOptional,
        });
      });

      console.log("Adding a rebuildingPackages/buildingFreshPackages step");
      steps.push(async (curr: number, total: number) => {
        this.reporter.step(
          curr,
          total,
          this.flags.force ? this.reporter.lang('rebuildingPackages') : this.reporter.lang('buildingFreshPackages'),
          emoji.get('page_with_curl'),
        );

        if (this.flags.ignoreScripts) {
          this.reporter.warn(this.reporter.lang('ignoredScripts'));
        } else {
          await this.scripts.init(flattenedTopLevelPatterns);
        }
      });

      if (this.flags.har) {
        console.log("Adding a savingHar (?) step");
        steps.push(async (curr: number, total: number) => {
          const formattedDate = new Date().toISOString().replace(/:/g, '-');
          const filename = `yarn-install_${formattedDate}.har`;
          this.reporter.step(
            curr,
            total,
            this.reporter.lang('savingHar', filename),
            emoji.get('black_circle_for_record'),
          );
          await this.config.requestManager.saveHar(filename);
        });
      }

      if (await this.shouldClean()) {
        console.log("Adding a cleaningModules step");
        steps.push(async (curr: number, total: number) => {
          this.reporter.step(curr, total, this.reporter.lang('cleaningModules'), emoji.get('recycle'));
          await clean(this.config, this.reporter);
        });
      }
    }

    console.log("About to step through the steps");
    let currentStep = 0;
    for (const step of steps) {
      const stepResult = await step(++currentStep, steps.length);
      console.log("Ran step " + currentStep);
      if (stepResult && stepResult.bailout) {
        this.maybeOutputUpdate();
        return flattenedTopLevelPatterns;
      }
    }

    console.log("Done with the steps");
    // fin!
    // The second condition is to make sure lockfile can be updated when running `remove` command.
    if (
      topLevelPatterns.length ||
      (await fs.exists(path.join(this.config.lockfileFolder, constants.LOCKFILE_FILENAME)))
    ) {
      await this.saveLockfileAndIntegrity(topLevelPatterns, workspaceLayout);
    } else {
      this.reporter.info(this.reporter.lang('notSavedLockfileNoDependencies'));
    }
    this.maybeOutputUpdate();
    this.config.requestManager.clearCache();
    return flattenedTopLevelPatterns;
  }

  /**
   * Check if we should run the cleaning step.
   */

  shouldClean(): Promise<boolean> {
    return fs.exists(path.join(this.config.lockfileFolder, constants.CLEAN_FILENAME));
  }

  /**
   * TODO
   */

  async flatten(patterns: Array<string>): Promise<Array<string>> {
    if (!this.flags.flat) {
      return patterns;
    }

    const flattenedPatterns = [];

    for (const name of this.resolver.getAllDependencyNamesByLevelOrder(patterns)) {
      const infos = this.resolver.getAllInfoForPackageName(name).filter((manifest: Manifest): boolean => {
        const ref = manifest._reference;
        invariant(ref, 'expected package reference');
        return !ref.ignore;
      });

      if (infos.length === 0) {
        continue;
      }

      if (infos.length === 1) {
        // single version of this package
        // take out a single pattern as multiple patterns may have resolved to this package
        flattenedPatterns.push(this.resolver.patternsByPackage[name][0]);
        continue;
      }

      const options = infos.map((info): ReporterSelectOption => {
        const ref = info._reference;
        invariant(ref, 'expected reference');
        return {
          // TODO `and is required by {PARENT}`,
          name: this.reporter.lang('manualVersionResolutionOption', ref.patterns.join(', '), info.version),

          value: info.version,
        };
      });
      const versions = infos.map((info): string => info.version);
      let version: ?string;

      const resolutionVersion = this.resolutions[name];
      if (resolutionVersion && versions.indexOf(resolutionVersion) >= 0) {
        // use json `resolution` version
        version = resolutionVersion;
      } else {
        version = await this.reporter.select(
          this.reporter.lang('manualVersionResolution', name),
          this.reporter.lang('answer'),
          options,
        );
        this.resolutions[name] = version;
      }

      flattenedPatterns.push(this.resolver.collapseAllVersionsOfPackage(name, version));
    }

    // save resolutions to their appropriate root manifest
    if (Object.keys(this.resolutions).length) {
      const manifests = await this.config.getRootManifests();

      for (const name in this.resolutions) {
        const version = this.resolutions[name];

        const patterns = this.resolver.patternsByPackage[name];
        if (!patterns) {
          continue;
        }

        let manifest;
        for (const pattern of patterns) {
          manifest = this.resolver.getResolvedPattern(pattern);
          if (manifest) {
            break;
          }
        }
        invariant(manifest, 'expected manifest');

        const ref = manifest._reference;
        invariant(ref, 'expected reference');

        const object = manifests[ref.registry].object;
        object.resolutions = object.resolutions || {};
        object.resolutions[name] = version;
      }

      await this.config.saveRootManifests(manifests);
    }

    return flattenedPatterns;
  }

  /**
   * Remove offline tarballs that are no longer required
   */

  async pruneOfflineMirror(lockfile: LockfileObject): Promise<void> {
    const mirror = this.config.getOfflineMirrorPath();
    if (!mirror) {
      return;
    }

    const requiredTarballs = new Set();
    for (const dependency in lockfile) {
      const resolved = lockfile[dependency].resolved;
      if (resolved) {
        const basename = path.basename(resolved.split('#')[0]);
        if (dependency[0] === '@' && basename[0] !== '@') {
          requiredTarballs.add(`${dependency.split('/')[0]}-${basename}`);
        }
        requiredTarballs.add(basename);
      }
    }

    const mirrorFiles = await fs.walk(mirror);
    for (const file of mirrorFiles) {
      const isTarball = path.extname(file.basename) === '.tgz';
      if (isTarball && !requiredTarballs.has(file.basename)) {
        await fs.unlink(file.absolute);
      }
    }
  }

  /**
   * Save updated integrity and lockfiles.
   */

  async saveLockfileAndIntegrity(patterns: Array<string>, workspaceLayout: ?WorkspaceLayout): Promise<void> {
    const resolvedPatterns: {[packagePattern: string]: Manifest} = {};
    Object.keys(this.resolver.patterns).forEach(pattern => {
      if (!workspaceLayout || !workspaceLayout.getManifestByPattern(pattern)) {
        resolvedPatterns[pattern] = this.resolver.patterns[pattern];
      }
    });

    // TODO this code is duplicated in a few places, need a common way to filter out workspace patterns from lockfile
    patterns = patterns.filter(p => !workspaceLayout || !workspaceLayout.getManifestByPattern(p));

    const lockfileBasedOnResolver = this.lockfile.getLockfile(resolvedPatterns);

    if (this.config.pruneOfflineMirror) {
      await this.pruneOfflineMirror(lockfileBasedOnResolver);
    }

    // write integrity hash
    await this.integrityChecker.save(
      patterns,
      lockfileBasedOnResolver,
      this.flags,
      workspaceLayout,
      this.scripts.getArtifacts(),
    );

    // --no-lockfile or --pure-lockfile or --frozen-lockfile flag
    if (this.flags.lockfile === false || this.flags.pureLockfile || this.flags.frozenLockfile) {
      return;
    }

    const lockFileHasAllPatterns = patterns.every(p => this.lockfile.getLocked(p));
    const lockfilePatternsMatch = Object.keys(this.lockfile.cache || {}).every(p => {
      return lockfileBasedOnResolver[p];
    });
    const resolverPatternsAreSameAsInLockfile = Object.keys(lockfileBasedOnResolver).every(pattern => {
      const manifest = this.lockfile.getLocked(pattern);
      return manifest && manifest.resolved === lockfileBasedOnResolver[pattern].resolved;
    });

    // remove command is followed by install with force, lockfile will be rewritten in any case then
    if (
      !this.flags.force &&
      this.lockfile.parseResultType === 'success' &&
      lockFileHasAllPatterns &&
      lockfilePatternsMatch &&
      resolverPatternsAreSameAsInLockfile &&
      patterns.length
    ) {
      return;
    }

    // build lockfile location
    const loc = path.join(this.config.lockfileFolder, constants.LOCKFILE_FILENAME);

    // write lockfile
    const lockSource = lockStringify(lockfileBasedOnResolver, false, this.config.enableLockfileVersions);
    await fs.writeFilePreservingEol(loc, lockSource);

    this._logSuccessSaveLockfile();
  }

  _logSuccessSaveLockfile() {
    this.reporter.success(this.reporter.lang('savedLockfile'));
  }

  /**
   * Load the dependency graph of the current install. Only does package resolving and wont write to the cwd.
   */
  async hydrate(ignoreUnusedPatterns?: boolean): Promise<InstallCwdRequest> {
    const request = await this.fetchRequestFromCwd([], ignoreUnusedPatterns);
    const {requests: depRequests, patterns: rawPatterns, ignorePatterns, workspaceLayout} = request;

    await this.resolver.init(depRequests, {
      isFlat: this.flags.flat,
      isFrozen: this.flags.frozenLockfile,
      workspaceLayout,
    });
    await this.flatten(rawPatterns);
    this.markIgnored(ignorePatterns);

    // fetch packages, should hit cache most of the time
    const manifests: Array<Manifest> = await fetcher.fetch(this.resolver.getManifests(), this.config);
    this.resolver.updateManifests(manifests);
    await compatibility.check(this.resolver.getManifests(), this.config, this.flags.ignoreEngines);

    // expand minimal manifests
    for (const manifest of this.resolver.getManifests()) {
      const ref = manifest._reference;
      invariant(ref, 'expected reference');
      const {type} = ref.remote;
      // link specifier won't ever hit cache
      let loc = '';
      if (type === 'link') {
        continue;
      } else if (type === 'workspace') {
        if (!ref.remote.reference) {
          continue;
        }
        loc = ref.remote.reference;
      } else {
        loc = this.config.generateHardModulePath(ref);
      }
      const newPkg = await this.config.readManifest(loc);
      await this.resolver.updateManifest(ref, newPkg);
    }

    return request;
  }

  /**
   * Check for updates every day and output a nag message if there's a newer version.
   */

  checkUpdate() {
    if (this.config.nonInteractive) {
      // don't show upgrade dialog on CI or non-TTY terminals
      return;
    }

    // don't check if disabled
    if (this.config.getOption('disable-self-update-check')) {
      return;
    }

    // only check for updates once a day
    const lastUpdateCheck = Number(this.config.getOption('lastUpdateCheck')) || 0;
    if (lastUpdateCheck && Date.now() - lastUpdateCheck < ONE_DAY) {
      return;
    }

    // don't bug for updates on tagged releases
    if (YARN_VERSION.indexOf('-') >= 0) {
      return;
    }

    this._checkUpdate().catch(() => {
      // swallow errors
    });
  }

  async _checkUpdate(): Promise<void> {
    let latestVersion = await this.config.requestManager.request({
      url: constants.SELF_UPDATE_VERSION_URL,
    });
    invariant(typeof latestVersion === 'string', 'expected string');
    latestVersion = latestVersion.trim();
    if (!semver.valid(latestVersion)) {
      return;
    }

    // ensure we only check for updates periodically
    this.config.registries.yarn.saveHomeConfig({
      lastUpdateCheck: Date.now(),
    });

    if (semver.gt(latestVersion, YARN_VERSION)) {
      const installationMethod = await getInstallationMethod();
      this.maybeOutputUpdate = () => {
        this.reporter.warn(this.reporter.lang('yarnOutdated', latestVersion, YARN_VERSION));

        const command = getUpdateCommand(installationMethod);
        if (command) {
          this.reporter.info(this.reporter.lang('yarnOutdatedCommand'));
          this.reporter.command(command);
        } else {
          const installer = getUpdateInstaller(installationMethod);
          if (installer) {
            this.reporter.info(this.reporter.lang('yarnOutdatedInstaller', installer));
          }
        }
      };
    }
  }

  /**
   * Method to override with a possible upgrade message.
   */

  maybeOutputUpdate() {}
  maybeOutputUpdate: any;
}

export function hasWrapper(commander: Object, args: Array<string>): boolean {
  return true;
}

export function setFlags(commander: Object) {
  commander.description('Yarn install is used to install all dependencies for a project.');
  commander.usage('install [flags]');
  commander.option('-g, --global', 'DEPRECATED');
  commander.option('-S, --save', 'DEPRECATED - save package to your `dependencies`');
  commander.option('-D, --save-dev', 'DEPRECATED - save package to your `devDependencies`');
  commander.option('-P, --save-peer', 'DEPRECATED - save package to your `peerDependencies`');
  commander.option('-O, --save-optional', 'DEPRECATED - save package to your `optionalDependencies`');
  commander.option('-E, --save-exact', 'DEPRECATED');
  commander.option('-T, --save-tilde', 'DEPRECATED');
}

export async function install(config: Config, reporter: Reporter, flags: Object, lockfile: Lockfile): Promise<void> {
  await wrapLifecycle(config, flags, async () => {
    const install = new Install(flags, config, reporter, lockfile);
    await install.init();
  });
}

export async function run(config: Config, reporter: Reporter, flags: Object, args: Array<string>): Promise<void> {
  let lockfile;
  let error = 'installCommandRenamed';
  console.log("Just entered run() in install.js");
  if (flags.lockfile === false) {
    lockfile = new Lockfile();
  } else {
    lockfile = await Lockfile.fromDirectory(config.lockfileFolder, reporter);
  }

  if (args.length) {
    const exampleArgs = args.slice();

    if (flags.saveDev) {
      exampleArgs.push('--dev');
    }
    if (flags.savePeer) {
      exampleArgs.push('--peer');
    }
    if (flags.saveOptional) {
      exampleArgs.push('--optional');
    }
    if (flags.saveExact) {
      exampleArgs.push('--exact');
    }
    if (flags.saveTilde) {
      exampleArgs.push('--tilde');
    }
    let command = 'add';
    if (flags.global) {
      error = 'globalFlagRemoved';
      command = 'global add';
    }
    throw new MessageError(reporter.lang(error, `yarn ${command} ${exampleArgs.join(' ')}`));
  }

  console.log("About to call the install.install() function");
  await install(config, reporter, flags, lockfile);
}

export async function wrapLifecycle(config: Config, flags: Object, factory: () => Promise<void>): Promise<void> {
  await config.executeLifecycleScript('preinstall');

  await factory();

  // npm behaviour, seems kinda funky but yay compatibility
  await config.executeLifecycleScript('install');
  await config.executeLifecycleScript('postinstall');

  if (!config.production) {
    if (!config.disablePrepublish) {
      await config.executeLifecycleScript('prepublish');
    }
    await config.executeLifecycleScript('prepare');
  }
}

{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "1.10";
      identifier = { name = "contra-tracer"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "2019 IOHK";
      maintainer = "operations@iohk.io";
      author = "Neil Davies, Alexander Diemand, Andreas Triantafyllos";
      homepage = "";
      url = "";
      synopsis = "A simple interface for logging, tracing or monitoring.";
      description = "";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          ] ++ (pkgs.lib).optional (compiler.isGhc && (compiler.version).lt "8.5") (hsPkgs.contravariant);
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "https://github.com/input-output-hk/iohk-monitoring-framework";
<<<<<<< HEAD
      rev = "dd30455144e11efb435619383ba84ce02aee720d";
      sha256 = "1g08bg99fvss99kg27l7pmxm7lh60573xln8l8x2rzvwfvfgk2i5";
=======
      rev = "ef164a834ef2b2d9ceb2ec262109a726ee534d66";
      sha256 = "0n6m65yfwsz37fpqv1f6sw5qrdh1hxiipss7yj1pvxdnya3ndnlc";
>>>>>>> 50731075... Update dependencies
      });
    postUnpack = "sourceRoot+=/contra-tracer; echo source root reset to \$sourceRoot";
    }
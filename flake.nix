{
  # Deliberately not "a library for a reduced augmented virtual double
  # ∞-category": that root is D-RT-16, which is provisional until M-F passes,
  # and flake metadata should not go stale when the root does.  This is
  # README.md's first sentence, which is not conditional on a gate.
  description = "Category Madness — a Lean 4 research library exploring a common, sealed interface for ordinary, enriched, internal, and higher category theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    # forester: the .tree -> hypertext builder for forest/.  Same input the
    # sibling math project uses, so the OCaml closure is shared.
    forester.url = "sourcehut:~jonsterling/ocaml-forester";
  };

  outputs =
    { self, nixpkgs, forester }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system nixpkgs.legacyPackages.${system});
    in
    {
      # `nix flake check` runs exactly the two network-free CI jobs from
      # .github/workflows/ci.yml -- the seal linter (D-TL-17 (1)-(3)) and the
      # forest checks (D-WF-09, D-WF-10, D-WF-12).  They are separate
      # derivations for the same reason CI splits them: a broken citation
      # graph and an import-ban violation are different failures and should
      # be reported by different things.
      #
      # The remaining CI jobs stay out on purpose.  `lake build`, swap_test.sh
      # and check_foundations.py resolve the pinned Mathlib over the network
      # and populate ~/.cache/mathlib; a fixed-output-free sandbox cannot do
      # that, and faking it with a permitted network would make the check
      # non-reproducible rather than merely slow.  Run those from the dev
      # shell.  The `citations` job reads GitHub PR metadata and has no
      # local analogue at all.
      checks = forAllSystems (
        system: pkgs:
        let
          lib = pkgs.lib;
          # Every gate script is stdlib Python that reads the tree and prints
          # a one-line verdict.  Keeping the transcript in the store path
          # means `nix log` is not the only record of what passed.
          gate =
            {
              name,
              fileset,
              commands,
            }:
            pkgs.stdenvNoCC.mkDerivation {
              inherit name;
              version = "0";
              src = lib.fileset.toSource {
                root = ./.;
                inherit fileset;
              };
              nativeBuildInputs = [ pkgs.python3 ];
              dontConfigure = true;
              buildPhase = ''
                runHook preBuild
                mkdir -p "$TMPDIR/log"
                ${lib.concatMapStrings (c: ''
                  echo "+ ${c}"
                  ${c} 2>&1 | tee -a "$TMPDIR/log/${name}.txt"
                '') commands}
                runHook postBuild
              '';
              installPhase = ''
                runHook preInstall
                mkdir -p "$out"
                cp "$TMPDIR/log/${name}.txt" "$out/"
                runHook postInstall
              '';
            };
          # The scripts are found by their own path, so scripts/ and mcp/ come
          # along with whatever they read.  Filtering to .py keeps swap_test.sh
          # and the audit .lean files -- which no gate here runs -- from
          # invalidating the build when they change.
          pySources = lib.fileset.unions [
            (lib.fileset.fileFilter (f: f.hasExt "py") ./scripts)
            (lib.fileset.fileFilter (f: f.hasExt "py") ./mcp)
          ];
        in
        {
          # D-TL-17 (1)-(3).  check_imports reads Theory/ and Interface-Stub/,
          # check_unfolding reads Theory/ and Interface/SEALED, and
          # check_statement_hygiene reads Interface/.
          seal = gate {
            name = "seal-linter";
            fileset = lib.fileset.unions [
              ./Interface
              ./Interface-Stub
              ./Theory
              pySources
            ];
            commands = [
              "python3 scripts/check_imports.py"
              "python3 scripts/check_unfolding.py"
              "python3 scripts/check_statement_hygiene.py"
            ];
          };

          # D-WF-09, D-WF-10, D-WF-12.  forest_check re-runs build_registry
          # --check itself, so forest/registry.json cannot drift from the
          # trees without failing here.  check_revision additionally reads
          # design/ for the revision lineage.
          forest = gate {
            name = "forest-checks";
            fileset = lib.fileset.unions [
              ./forest
              ./design
              pySources
            ];
            commands = [
              "python3 scripts/forest_check.py"
              "python3 scripts/check_revision.py"
              "python3 mcp/server.py --selftest"
            ];
          };
        }
      );

      devShells = forAllSystems (
        system: pkgs: {
          # Everything AGENTS.md §3 asks you to run before submitting, plus the
          # tools for reading the repository and talking to GitHub.
          #
          # Lean is deliberately *not* a nix package here.  lean-toolchain pins
          # leanprover/lean4:v4.33.1 and lakefile.toml pins Mathlib to the
          # matching v4.33.1 tag (D-CH-24); elan reads that pin, and `lake exe
          # cache get` fetches Mathlib's prebuilt oleans into ~/.cache/mathlib.
          # nixpkgs' leanPackages carries a different Lean/Mathlib pair, so
          # using it would either contradict the recorded pin or force a
          # from-source Mathlib rebuild.  nixpkgs' elan patches the binaries it
          # downloads (its 0001-dynamically-patchelf-binaries patch bakes in
          # patchelf, cc, ar and the dynamic linker), so the elan-managed
          # toolchain runs on NixOS without a nix-ld shim -- which is what
          # docs/CONTAINER_SETUP.md's LD_PRELOAD workaround exists to
          # substitute for on a container that has no elan at all.
          default = pkgs.mkShell {
            packages = [
              pkgs.elan

              # Every gate script and mcp/server.py; stdlib only.
              pkgs.python3

              # forester builds forest/ into hypertext.  forest.toml names a
              # theme = "theme" directory this repository does not contain and
              # does not pin (see docs/CONTAINER_SETUP.md), so `forester build
              # forest.toml` does not work yet and there is no forest package
              # or check here.  forester is in the shell so the theme can be
              # obtained and pinned; until then the structural gates above are
              # what actually verifies the forest.
              forester.packages.${system}.default

              # lake resolves the Mathlib dependency over git, and Mathlib's
              # cache tool fetches oleans over https.
              pkgs.git
              pkgs.curl
              pkgs.cacert

              pkgs.gh
              pkgs.ripgrep
              pkgs.jq
            ];

            # Named rather than left to the ambient environment: lake fetches
            # Mathlib over git and its cache tool fetches oleans over https,
            # and both are the first thing a fresh checkout does.  A shell
            # that only works because the host happened to export a cert
            # bundle is not a reproducible shell.
            SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
            NIX_SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";

            shellHook = ''
              echo "category-madness: Lean is elan-managed (lean-toolchain pins v4.33.1)." >&2
              echo "  first build:  lake exe cache get && lake build" >&2
              echo "  gates:        nix flake check   (seal linter + forest checks)" >&2
            '';
          };
        }
      );

      formatter = forAllSystems (system: pkgs: pkgs.nixfmt-rfc-style);
    };
}

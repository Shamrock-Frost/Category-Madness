# Lean and Forester in this container

This note is for the Work Mode container used by this repository. It keeps tools
inside the workspace so the setup does not rely on a global toolchain or modify the
container image.

## Lean 4.33.1

The project pins Lean in `lean-toolchain`:

```text
leanprover/lean4:v4.33.1
```

The container does not provide `elan`, `lake`, or `lean` on `PATH`. Download the
matching official Linux release and unpack it below the workspace:

```sh
TOOLCHAIN_ROOT="$PWD/../toolchains"
mkdir -p "$TOOLCHAIN_ROOT"
curl --fail --location --silent --show-error \
  https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst \
  -o "$TOOLCHAIN_ROOT/lean-4.33.1-linux.tar.zst"
tar --no-same-owner --zstd -xf "$TOOLCHAIN_ROOT/lean-4.33.1-linux.tar.zst" -C "$TOOLCHAIN_ROOT"
```

`tar --no-same-owner` matters in this container: the release archive contains ownership
metadata that the workspace filesystem cannot apply.

Lean locates itself through `/proc/<pid>/exe`. This container does not expose that path,
so use the following small preload shim. It substitutes the kernel-provided executable
path only for that lookup and delegates all other `readlink` calls unchanged:

```sh
cat > "$TOOLCHAIN_ROOT/executable_path.c" <<'EOF'
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <sys/auxv.h>
#include <unistd.h>

ssize_t readlink(const char *path, char *buffer, size_t size) {
  char self_exe[64];
  snprintf(self_exe, sizeof(self_exe), "/proc/%ld/exe", (long)getpid());
  if (strcmp(path, "/proc/self/exe") == 0 || strcmp(path, self_exe) == 0) {
    const char *exe = (const char *)getauxval(AT_EXECFN);
    if (exe != NULL) {
      size_t length = strlen(exe);
      if (length > size) length = size;
      memcpy(buffer, exe, length);
      return (ssize_t)length;
    }
  }
  ssize_t (*original)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
  return original(path, buffer, size);
}
EOF
gcc -shared -fPIC "$TOOLCHAIN_ROOT/executable_path.c" -ldl \
  -o "$TOOLCHAIN_ROOT/executable_path.so"
```

Define this command prefix from the repository root:

```sh
export CATEGORY_MADNESS_LEAN_ENV="LD_PRELOAD=$TOOLCHAIN_ROOT/executable_path.so \
LD_LIBRARY_PATH=$TOOLCHAIN_ROOT/lean-4.33.1-linux/lib/lean:$TOOLCHAIN_ROOT/lean-4.33.1-linux/lib \
PATH=$TOOLCHAIN_ROOT/lean-4.33.1-linux/bin:$PATH"
```

Then verify and build:

```sh
env $CATEGORY_MADNESS_LEAN_ENV lean --version
env $CATEGORY_MADNESS_LEAN_ENV lake build
env $CATEGORY_MADNESS_LEAN_ENV bash scripts/swap_test.sh
```

The first Lake run resolves the pinned Mathlib dependency. It may offer to download
Mathlib's compiled cache. That cache is optional for this project; to skip it during a
fresh dependency update, use:

```sh
env $CATEGORY_MADNESS_LEAN_ENV MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
```

Do not copy the shim or a downloaded Lean release into this repository. Both belong in
the workspace-level `toolchains/` directory and are local container accommodation,
rather than project dependencies.

## Forester 5

Forester is an OCaml program. The current `forester.5.0` opam package requires OCaml
5.3 or newer. This container currently has neither `opam` nor `forester`. If system
package installation is available, first install the host prerequisites appropriate to
the base image: a C compiler/build tools, `pkg-config`, `m4`, `opam`, and any LaTeX
tools needed by the selected theme. On Debian/Ubuntu that is commonly:

```sh
sudo apt-get update
sudo apt-get install -y build-essential pkg-config m4 opam
```

Initialize opam without its sandbox: nested sandboxing is commonly unavailable in a
container. Create a project-local switch with a version satisfying Forester 5:

```sh
opam init --bare --disable-sandboxing --yes
opam switch create . 5.3.0 --yes
eval "$(opam env)"
opam install forester.5.0 --yes
forester --version
```

Keep the switch local to the checkout. Re-enter it later with:

```sh
eval "$(opam env --switch=. --set-switch)"
```

Run the document build from the repository root:

```sh
forester build forest.toml
```

`forest.toml` uses the handwritten `forest/` trees plus generated `build/forest/` trees
and declares `theme = "theme"`. This repository currently does not contain that theme
directory or a pinned source URL for it. Obtain the intended Forester-5-compatible theme
before treating a successful build as reproducible, then record its exact repository and
commit in the project. Until then, run the structural checks that do not depend on
Forester:

```sh
python3 scripts/build_registry.py --check
python3 scripts/forest_check.py
python3 scripts/check_revision.py
python3 mcp/server.py --selftest
```

The project should add the theme source and a version pin before enabling `forester build`
as a CI gate. Forester installation itself is not a substitute for that missing input.

## Sources

- Lean release: <https://github.com/leanprover/lean4/releases/tag/v4.33.1>
- Forester package and dependencies: <https://opam.ocaml.org/packages/forester/>
- Forester installation and build usage: <https://ocaml.org/p/forester/4.3.1>

Cites: D-CH-24, D-TL-17, D-WF-09, D-WF-14.

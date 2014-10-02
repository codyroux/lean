[msys2]: http://msys2.github.io
[pacman]: https://wiki.archlinux.org/index.php/pacman

Lean for Windows
----------------

A native Lean binary for Windows can be generated using [msys2].
It is easy to install all dependencies, it produces native
64/32-binaries, and supports a C++11 compiler.


## Installing dependencies

[The official webpage][msys2] provides one-click installers.
We assume that you install [msys2][msys2] at `c:\msys64`.
Once installed it, you can run msys2 shell from the start menu.
It has a package management system, [pacman][pacman], which is used in Arch Linux.

Here are the commands to install all dependencies needed to compile Lean on your machine.

```bash
# Update Packages
pacman -Syu

# Install gcc (4.9.1)
pacman -Su mingw-w64-x86_64-gcc

# Install mpfr, gmp, lua
pacman -Su mingw-w64-x86_64-mpfr mingw-w64-x86_64-gmp mingw-w64-x86_64-lua

# Install python, ninja, gdb, cmake
pacman -Su python2 mingw-w64-x86_64-ninja mingw-w64-x86_64-gdb mingw-w64-x86_64-cmake

# Install git
pacman -Su git
```
Make sure that you add `c:\msys64\mingw64\bin` into the `PATH` environment variable.

## Build Lean

We assume that you already check out Lean at `c:\lean` directory. In the [msys2] shell,
execute the following commands.

```bash
cd /c/lean/
mkdir build && cd build
cmake -D CMAKE_CXX_COMPILER=g++.exe -G Ninja ../src
ninja
```

## Build Lean using Boost

To install Boost in the [msys2] shell, use the following command:

```bash
pacman -S mingw-w64-x86_64-boost
```

In the [msys2] shell, execute the following commands.

```bash
cd /c/lean/
mkdir build && cd build
cmake -D CMAKE_CXX_COMPILER=g++.exe -D BOOST=ON -G Ninja ../src
ninja
```
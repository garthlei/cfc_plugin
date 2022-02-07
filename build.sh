#!/usr/bin/env bash
g++ -I`riscv64-unknown-elf-gcc -print-file-name=plugin`/include -I/usr/local/include -dynamiclib -undefined dynamic_lookup -fPIC -fno-rtti -o plugin.dylib plugin.cc

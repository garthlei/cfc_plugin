#!/usr/bin/env bash
x86_64-w64-mingw32-g++ -I$GCC_WIN32_PLUGIN_PATH/include -shared -fPIC -fno-rtti -o plugin.dll plugin.cc $GCC_WIN32_PLUGIN_PATH/cc1.exe.a

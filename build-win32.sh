#!/usr/bin/env bash
x86_64-w64-mingw32-g++ -I$GCC_WIN32_PLUGIN_PATH/include -shared -Wl,--export-all-symbols -o plugin.dll plugin.cc func.cpp $GCC_WIN32_PLUGIN_PATH/cc1.exe.a

#!/usr/bin/env bash
x86_64-w64-mingw32-g++ -I$GCC_WIN32_PLUGIN_PATH/include -shared -fPIC -fno-rtti -o plugin.dll plugin.cc func.cpp $GCC_WIN32_PLUGIN_PATH/cc1plus.exe.a

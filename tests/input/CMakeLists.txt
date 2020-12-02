# Don't remove me
cmake_minimum_required (VERSION 3.12 FATAL_ERROR) # 3.12 is mandatory since we rely on NEW behaviour for CMP0074
if (${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.13.0")
  cmake_policy(SET CMP0077 OLD) # option() honors normal behaviour. This was introduced in CMake 3.13.
                                # Use the old policy to retain compatability with 3.12.
endif()

cmake_policy(SET CMP0074 NEW) # find_package() uses <PackageName>_ROOT variables.

##
## Copyright (c) 2012-2014 ThisNiceCompany.
##
## This file is part of ProjectName 
## (see http://the.projectname.com).
##
## This program is free software: you can redistribute it and/or modify
## it under the terms of the GNU Lesser General Public License as published by
## the Free Software Foundation, either version 3 of the License, or
## (at your option) any later version.
##
## This program is distributed in the hope that it will be useful,
## but WITHOUT ANY WARRANTY; without even the implied warranty of
## MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
## GNU Lesser General Public License for more details.
##
## You should have received a copy of the GNU Lesser General Public License
## along with this program. If not, see <http://www.gnu.org/licenses/>.
##

# Don't remove me
cmake_minimum_required (VERSION 3.12 FATAL_ERROR) # 3.12 is mandatory since we rely on NEW behaviour for CMP0074
if (${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.13.0")
  cmake_policy(SET CMP0077 OLD) # option() honors normal behaviour. This was introduced in CMake 3.13.
                                # Use the old policy to retain compatability with 3.12.
endif()

cmake_policy(SET CMP0074 NEW) # find_package() uses <PackageName>_ROOT variables.

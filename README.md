# licenseheaders

[![PyPi version](https://img.shields.io/pypi/v/licenseheaders.svg)](https://pypi.python.org/pypi/licenseheaders/)
[![Python compatibility](https://img.shields.io/pypi/pyversions/licenseheaders.svg)](https://pypi.python.org/pypi/licenseheaders/)

A Python 3 tool to update, change or add license headers to all files of any of 
the supported types (see below) in or below some directory.

## Usage

```
usage: licenseheaders [-h] [-V] [-v] [-d DIR] [-b] [-t TMPL] [-y YEARS]
                         [-o OWNER] [-n PROJECTNAME] [-u PROJECTURL]
                         [--enc ENCODING] [--safesubst] [-D]
                         [--additional-extensions ADDITIONAL_EXTENSIONS [ADDITIONAL_EXTENSIONS ...]]

Python license header updater

optional arguments:
  -h, --help            show this help message and exit
  -V, --version         show program's version number and exit
  -v, --verbose         increases log verbosity (can be specified 1 to 3
                        times, default shows errors only)
  -d DIR, --dir DIR     The directory to recursively process (default: .).
  -b                    Back up all files which get changed to a copy with
                        .bak added to the name
  -t TMPL, --tmpl TMPL  Template name or file to use.
  -y YEARS, --years YEARS
                        Year or year range to use.
  -o OWNER, --owner OWNER
                        Name of copyright owner to use.
  -n PROJECTNAME, --projname PROJECTNAME
                        Name of project to use.
  -u PROJECTURL, --projurl PROJECTURL
                        Url of project to use.
  --enc ENCODING        Encoding of program files (default: utf-8)
  --dry                 Only show what would get done, do not change any files
  --safesubst           Do not raise error if template variables cannot be
                        substituted.
  -D                    Enable debug messages (same as -v -v -v)
  -E [EXT [EXT ...]], --ext [EXT [EXT ...]]
                        If specified, restrict processing to the specified
                        extension(s) only
  --additional-extensions ADDITIONAL_EXTENSIONS [ADDITIONAL_EXTENSIONS ...]
                        Provide a comma-separated list of additional file
                        extensions as value for a specified language as key,
                        each with a leading dot and no whitespace (default:
                        None).
  -x [EXCLUDE [EXCLUDE ...]], --exclude [EXCLUDE [EXCLUDE ...]]
                        File path patterns to exclude


Known extensions: ['.java', '.scala', '.groovy', '.jape', '.js', '.sh', '.csh', '.py', '.pl', '.pl', '.robot', '.xml', '.sql', '.c', '.cc', '.cpp', 'c++', '.h', '.hpp', '.rb', '.cs', '.vb', '.erl', '.src', '.config', '.schema']

If -t/--tmpl is specified, that header is added to (or existing header replaced for) all source files of known type
If -t/--tmpl is not specified byt -y/--years is specified, all years in existing header files
  are replaced with the years specified

Examples:
  # add a lgpl-v3 header and set the variables for year, owner, project and url to the given values
  # process all files in the current directory and below
  licenseheaders -t lgpl-v3 -y 2012-2014 -o ThisNiceCompany -n ProjectName -u http://the.projectname.com
  # only update the year in all existing headers
  # process all files in the current directory and below
  licenseheaders -y 2012-2015
  # only update the year in all existing headers, process the given directory
  licenseheaders -y 2012-2015 -d /dir/where/to/start/
  # apply copyright headers to files specified by their language family + file extensions
  licenseheaders -y 2012-2015 -d /dir/where/to/start/ --additional-extensions python=.j2
  licenseheaders -y 2012-2015 -d /dir/where/to/start/ --additional-extensions python=.j2,.tpl script=.txt
```

If *licenseheaders* is installed as a package (from pypi for instance), one can interact with it as a command line tool:

```
python -m licenseheaders -t lgpl3 -o "Eager Hacker"
```

or directly:

```
licenseheaders -t lgpl3 -o "Eager Hacker"
```


# Installation

NOTE: this requires Python 3.5 or higher!

```
pip install licenseheaders
```

IMPORTANT: do *NOT* download from the github releases page, these stopped to get updated after release 0.5
when the package became available on PyPi. Since then installation with `pip install` is recommended.


## Template names and files

This library comes with a number of predefined templates. If a template name is specified
which when matched against all predefined template names matches exactly one as a substring,
then that template is used. Otherwise the name is expected to be the path of file.

If a template does not contain any variables of the form `${varname}` it is used as is.
Otherwise the program will try to replace the variable from one of the following 
sources:

- an environment variable with the same name but the prefix `LICENSE_HEADERS_` added
- the command line option that can be used to set the variable (see usage)


## Supported file types and how they are processed

*NOTE:* You can provide additional file extensions with `--additional-extensions` cli argument.
Note that file extensions which contain multiple dots, e.g. ".py.j2", are not yet supported,
use ".j2" at the moment instead.

java:
- extensions .java, .scala, .groovy, .jape, .js
- also used for Javascript
- only headers that use Java block comments are recognised as existing headers
- the template text will be wrapped in block comments

script:
- extensions .sh, .csh

perl:
- extension .pl

python:
- extension .py

xml:
- extension .xml

sql:
- extension .sql

c:
- extensions .c, .cc, .cpp, .c++, .h, .hpp

ruby:
- extension .rb

csharp:
- extension .cs

visualbasic:
- extension .vb

erlang:
- extensions .erl, .src, .config, .schema

html:
- extensions .html

css:
- extensions .css, .scss, .sass

docker:
- extensions .dockerfile
- filenames Dockerfile

yaml:
- extensions .yaml, .yml

zig:
- extensions .zig

## License

Licensed under the term of `MIT License`. See file [LICENSE.txt](LICENSE.txt).



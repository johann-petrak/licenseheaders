.. image:: https://img.shields.io/pypi/v/licenseheaders.svg
    :target: https://pypi.python.org/pypi/licenseheaders/
    :alt: PyPi version

.. image:: https://img.shields.io/pypi/pyversions/licenseheaders.svg
    :target: https://pypi.python.org/pypi/licenseheaders/
    :alt: Python compatibility
 	
.. image:: https://img.shields.io/travis/elmotec/licenseheaders.svg
    :target: https://travis-ci.org/elmotec/licenseheaders
    :alt: Build Status

.. image:: https://img.shields.io/pypi/dm/licenseheaders.svg
    :alt: PyPi
    :target: https://pypi.python.org/pypi/licenseheaders

.. image:: https://coveralls.io/repos/elmotec/licenseheaders/badge.svg
    :target: https://coveralls.io/r/elmotec/licenseheaders
    :alt: Coverage
    
.. image:: https://img.shields.io/codacy/474b0af6853a4c5f8f9214d3220571f9.svg
    :target: https://www.codacy.com/app/elmotec/licenseheaders/dashboard
    :alt: Codacy


========
licenseheaders
========

A tool to update, change or add license headers to all files of any of 
the supported types in or below some directory.

Currently, the following file types are supported: Java/Scala/Groovy, bash/sh/csh, ...


Usage
-----

::

  usage: licenseheaders.py [-h] [-v] [-V] [-d directory] [-t template] [-y years] [-b] [-a]
                            [-c copyrightOwner] 

  License Header Updater

  positional arguments: none

  optional arguments:
    -h, --help            Show this help message and exit
    -V, --version         Show program's version number and exit
    -v, --verbose         Increases log verbosity (can be specified multiple times)
    -d, --dir DIR         Directory to process, all subdirectories will be included
    -t, --tmpl TMPL       Template name or file to use (if not specified, -y must be specified)
    -y, --years YEARS     If template is specified, the year to substitute, otherwise this year
                          or year range will replace any existing year in existing headers.
                          Replaces variable ${years} in a template
    -b, --backup          For each file that gets changed, create a backup of the original with
                          the additional filename extension .bak
    -c, --cr CO           Set copyright owner to CO, replaces variable ${owner} in a template
    -a, --addonly         add a header to all supported file types, ignore any existing headers.
        --enc ENC         Use file encoding ENC instead of UTF-8 for the program files.

  Examples:
  # Add a new license header or replace any existing one based on the lgpl3 template.
  # Process all files of supported type in or below the current directory.
  # Use "Eager Hacker" as the copyright owner.
  licenseheaders.py -t lgpl3 -c "Eager Hacker"


If licenseheaders is installed as a package (from pypi for instance), one can interact with it as a command line tool:

::

  python -m licenseheaders -t lgpl3 -c "Eager Hacker"

or directly:

::

  licenseheaders -t lgpl3 -c "Eager Hacker"  



Installation
------------

Download ``licenseheaders.py`` from ``http://github.com/johann-petrak/licenseheaders`` or :

::

  pip install licenseheaders


Template names and files
------------------------

This library comes with a number of predefined templates. If a template name is specified
which when matched against all predefined template names matches exactly one as a substring,
then that template is used. Otherwise the name is expected to be the path of file.

If a template does not contain any variables of the form `${varname}` it is used as is.
Otherwise the program will try to replace the variable from one of the following 
sources:

- an environment variable with the same name but the prefix `LICENSE_HEADERS_` added
- the command line option that can be used to set the variable (see usage)


Supported file types and how they are processed
-----------------------------------------------

Java:
- assumed for all files with the extensions: .java, .scala, .groovy
- only headers that use Java block comments are recognised as existing headers
- the template text will be wrapped in block comments

License
-------

Licensed under the term of `MIT License`_. See attached file LICENSE.txt.


.. _MIT License: http://en.wikipedia.org/wiki/MIT_License


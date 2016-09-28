.. image:: https://img.shields.io/pypi/v/license-headers.svg
    :target: https://pypi.python.org/pypi/license-headers/
    :alt: PyPi version

.. image:: https://img.shields.io/pypi/pyversions/license-headers.svg
    :target: https://pypi.python.org/pypi/license-headers/
    :alt: Python compatibility
 	
.. image:: https://img.shields.io/travis/elmotec/license-headers.svg
    :target: https://travis-ci.org/elmotec/license-headers
    :alt: Build Status

.. image:: https://img.shields.io/pypi/dm/license-headers.svg
    :alt: PyPi
    :target: https://pypi.python.org/pypi/license-headers

.. image:: https://coveralls.io/repos/elmotec/license-headers/badge.svg
    :target: https://coveralls.io/r/elmotec/license-headers
    :alt: Coverage
    
.. image:: https://img.shields.io/codacy/474b0af6853a4c5f8f9214d3220571f9.svg
    :target: https://www.codacy.com/app/elmotec/license-headers/dashboard
    :alt: Codacy


========
license-headers
========

A tool to update, change or add license headers to all files of any of 
the supported types in or below some directory.

Currently, the following file types are supported: Java/Scala/Groovy, bash/sh/csh, ...


Usage
-----

::

  usage: license-headers.py [-h] [-v] [-V] [-d directory] [-t template] [-y years] [-b] [-a]
                            [-c copyrightOwner] 

  License Header Updater

  positional arguments: none

  optional arguments:
    -h, --help            show this help message and exit
    -V, --version         show program's version number and exit
    -v, --verbose         increases log verbosity (can be specified multiple times)
    -d, --dir             directory to process, all subdirectories will be included
    -t, --tmpl            template name or file to use (if not specified, -y must be specified)
    -y, --years           if template is specified, the year to substitute, otherwise this year
                          or year range will replace any existing year in existing headers.
                          Replaces variable ${years} in a template
    -b, --backup          for each file that gets changed, create a backup of the original with
                          the additional filename extension .bak
    -c, --cr              copyright owner, replaces variable ${owner} in a template
    -a, --addonly         add a header to all supported file types, ignore any existing headers.

  Examples:
  # Add a new license header or replace any existing one based on the lgpl3 template.
  # Process all files of supported type in or below the current directory.
  # Use "Eager Hacker" as the copyright owner.
  license-headers.py -t lgpl3 -c "Eager Hacker"


If license-headers is installed as a package (from pypi for instance), one can interact with it as a command line tool:

::

  python -m license-headers -t lgpl3 -c "Eager Hacker"


Installation
------------

Download ``license-headers.py`` from ``http://github.com/johann-petrak/license-headers`` or :

::

  pip install license-headers


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


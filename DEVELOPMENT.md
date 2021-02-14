# NOTES ON DEVELOPMENT

* Created two branches
  * version-0.8.x : for continuing development/improving the "OLD" version as released on pypi
  * version-1.0.x : to start developing the new version with some bigger changes:
    * different project layout
    * use config files more
    * maybe use templates with conditional sections?
    * use subcommands for updating, adding, replacing templates
    * better heuristics to identify existing templates: if we know the template, we can find 
      by looking for the fixed parts!
    * better heuristics for where to place a new license header: after certain fixed top lines but before other certain lines
* master now still coincides with the version-0.8.x branch 


## 1.0.x version

* make clear what action(s) to perform:
  * update existing license header with new date
  * replace existing LH block with new one
  * insert LH block if missing
  * remove LH block
  * in practice we probably either want to update the date, remove, or perform insert/replace 
* clearly define the heuristics for finding 
  * either an existing license header 
  * or the position where one should get inserted if not found
* clearly define how the files to process are found:
  * either find files matching inside a directory tree
    * use something like the gitignore strategy to match/ignore?
  * or process a pre-configured list of files (either from command line or a file containing the paths)
* for each "type" of file, have a preconfigured way for how to match such a file and how to 
  LH blocks are formatted. Optionally also define ways to identify a LH block:
  * pattern for something inside the block
  * pattern specifically for the start of a block
  * pattern specifically for the end of a block
  * all given patterns must match, if start/end is missing, the default heuristic for finding is used
  * the above is only used to match any LH, if we cannot match a specific, given LH from a template
* each processed file is loaded into memory until we have enough lines to find out if it needs to get changed or not
  * if it gets changed, the original file is moved to a backup version, then the changed part is written, then the rest is written to the
    original file name. If backup is false, the renamed file is removed
    (if initially the backup file is present, it is overridden unless configured to fail)
* When the tool is run, the files to process are specified either as a list of files with optional file type to use for the file or 
  as a directory plus the types to match.
  * There is a default list of type definitions, but a config file can add to or completely replace those definitions
  * everything that can be specified on the command line can be specified in the config file, including the action
  * config files can be auto-detected based on standard names in standard places
  * once command line and config file has been specified, the tool determines if something is missing or contradictory
* templates: maybe use more advanced templates, allow arbitrary variables which can be set from config files or command line using something like 
  `-Dvar=...` or similar. 
  * ideally, we can know programmatically which variables a template has, if not, expect all variables to be defined in the config or by default!
  * to match a LH, generate regexp from it, where the variables get replaced by non greedy arbitrary string matcher: that way we can match a specific template for updating
 

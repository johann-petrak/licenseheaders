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

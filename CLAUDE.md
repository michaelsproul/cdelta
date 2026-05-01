* Don't worry about GPG signed commits, just skip signing.
* Avoid using background jobs to build, they have a tendancy to pile up and consume resources.
  You do not have access to `kill` to clean up, so just run in the foreground.
* Pipe build output to files so you don't need to re-run build commands. Avoid piping directly to
  head, tail, etc.
* Always use `-o system_log=true -v` flags with `isabelle build` to be able to detect stuckness.
* Never use `is` as a variable name

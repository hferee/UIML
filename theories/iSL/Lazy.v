Definition Lazy T := unit -> T.
Notation "'lazy' x" := (fun _ : unit => x) (x at next level, at level 50).
Notation "'force' x" := (x tt) (x at next level, at level 50).
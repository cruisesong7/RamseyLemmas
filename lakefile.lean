import Lake
open Lake DSL

package "Ramsey_2lemmas" where
  -- add package configuration options here

@[default_target]

lean_lib «Ramsey2lemmas» where
  -- add library configuration options here

require formal_ramsey from git "https://github.com/cruisesong7/formal_ramsey"@"9ecbb4f"

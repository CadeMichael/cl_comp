import Lake
open Lake DSL

package "StackComp" where
  -- add package configuration options here

lean_lib «StackComp» where
  -- add library configuration options here

@[default_target]
lean_exe "stackcomp" where
  root := `Main

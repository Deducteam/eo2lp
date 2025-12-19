
We need to implement a mechanism for binding free schematic
variables in post-elaboration commands. e.g.;
```
Elaborating: (define @pair () @@pair)

  Begin resolving `@@pair⟨U ↦ ?U0, T ↦ ?T0⟩`
  Resolved:
    `@@pair⟨U ↦ ?U0, T ↦ ?T0⟩`
  with type
    `(~> ?U0 ?T0 ((@Pair⟨⟩ ⋅ ?U0) ⋅ ?T0))`

Done:
  define @pair⟨⟩
    : (~> ?U0 ?T0 ((@Pair⟨⟩ ⋅ ?U0) ⋅ ?T0))
    := @@pair⟨U ↦ ?U0, T ↦ ?T0⟩
```

We need to update the signature so that @pair has two
parameters {U, T} and then update the body of the
definition with this assignment.

Some procedure called 'bind_svars'.
For each free schematic var, we choose a name.

  SVar (s,0) -> Var s
  SVar (s,i) -> Var (s ^ string_of_int i)

We use this list of variables as our (implicit) parameters for @@pair.
Then we replace the schematic vars in the body with our choice
using `svmap_subst`.

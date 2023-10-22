# Mathlib Template

This sets up a basic Mathlib project on your machine. If you first need to install Lean 4, you can do so by following the instructions on this basic [Lean Template](https://github.com/matematiflo/LeanTemplate) repository.

## Install instructions

### Clone the repo

Clone the present repository.

```script
https://github.com/matematiflo/MathlibTemplate.git
```

### Download the Mathlib binaries

> For the following step, it might be better to not use the terminal from within VS Code (which might generate error messages until the binaries have ben downloaded).

From a terminal, run the command line

```script
lake exe cache get
```

This downloads the Mathlib binaries, so you can avoid building Mathlib locally (which takes a long time). In principle, though, this can be done via the command `lake build`.

### Go to the test file

Go to the file [MathlibTest.lean](MathlibTest.lean) and check that there are no error messages (the file imports the file `Mathlib.Algebra.Group.Defs` of the Mathlib library, which should only take a few seconds).

```lean
import Mathlib.Algebra.Group.Defs

example (G : Type) [Group G] : 1 * 1 = 1 := by {rfl}

example : 1 + 1 = 2 := refl 2
example : 1 + 1 = 2 := refl (1 +1)
example : 1 + 1 = 2 := rfl  -- same as `refl 2`, with the argument taken implicitly

example : 1 = 1 := by {exact refl 1}  -- in tactic mode
```

When you position your cursor at the end of the first `example` line (for instance immediately after the `by {rfl}`), you should see the following message in the Lean Infoview panel (which in principle opens automatically to the right).

> **No goals**

This example gives a proof that, in a group `G`, the neutral element `1` satisfies `1 * 1 = 1`, by definition :-)

The other four exampples are just different ways of writing a proof that `1 + 1 = 2`. Again, it holds by definition.

## Troubleshooting and updating

If you get error messages when parsing `MathlibTest.lean`, or if you want to update Mathlib, run the following three commands (one after the other).

```script
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
lake exe cache get
```

Then close the file `MathlibTest.lean` and open it again.

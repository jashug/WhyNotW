To compile, simply run `make` in this the `code` subdirectory with Coq (8.12) on your path or with environment variable `COQBIN` set. This may take an hour or two to compile, due to some slow files dealing with bootstrapping.

* `Nat.v` contains the special case of the construction of the natural numbers
* `General.v` works out the machinery for the general case
* `TestGeneral.v` applies the general construction to several specific inductives
  and checks that we get the expected computational behavior.
  This includes the type `Code` itself, demonstrating that bootstrapping should be possible.
* `Bootstrap.v` defines `Code` explicitly in terms of `W` types, and then defines the rest of the general
  construction on top. This is much slower than `General.v`, taking about half an hour to compile on my machine.
  `TestBootstrap/Nat.v` applies the general construction in `Bootstrap.v` to the natural numbers
  (about 20 minutes to compile). `TestBootstrap/TiedKnot.v` checks that `Code = El "Code"`.

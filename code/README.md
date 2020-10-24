* `Nat.v` contains the special case of the construction of the natural numbers
* `General.v` works out the machinery for the general case
* `TestGeneral.v` applies the general construction to several specific inductives
  and checks that we get the expected computational behavior.
  This includes the type `Code` itself, demonstrating that bootstrapping should be possible.
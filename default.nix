{ mkDerivation, aeson, base, constraints, constraints-extras
, dependent-map, dependent-sum, dependent-sum-aeson-orphans, stdenv
}:
mkDerivation {
  pname = "dependent-monoidal-map";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    aeson base constraints constraints-extras dependent-map
    dependent-sum dependent-sum-aeson-orphans
  ];
  description = "Data.Dependent.Map variant that appends conflicting entries when merging maps instead of discarding one side of the conflict.";
  license = stdenv.lib.licenses.bsd3;
}

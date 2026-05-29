LoadPackage("sla");


I := E(4);;

RealPartQI := function(z)
  return (z + GaloisCyc(z,-1))/2;
end;;

ImagPartQI := function(z)
  return (z - GaloisCyc(z,-1))/(2*I);
end;;

SplitQIList := function(row)
  return Concatenation(
    List(row, RealPartQI),
    List(row, ImagPartQI)
  );
end;;

CompactRealBasisSU := function(g)
  local cb, ep, fm, hh, kB, r;

  cb := ChevalleyBasis(g);

  ep := cb[1];  # positive root vectors e_alpha
  fm := cb[2];  # negative root vectors f_alpha
  hh := cb[3];  # Cartan basis h_i

  kB := [];

  # e_alpha - f_alpha
  for r in [1..Length(ep)] do
    Add(kB, ep[r] - fm[r]);
  od;

  # i(e_alpha + f_alpha)
  for r in [1..Length(ep)] do
    Add(kB, I*(ep[r] + fm[r]));
  od;

  # i h_i
  for r in [1..Length(hh)] do
    Add(kB, I*hh[r]);
  od;

  return kB;
end;;

CompactStabilizerAlgebra := function(v, g, V)
  local bV, kB, mC, mR, sol, stab;

  bV := Basis(V);
  kB := CompactRealBasisSU(g);

  # Rows are x.v for compact basis elements x.
  mC := List(kB, x -> Coefficients(bV, x^v));

  # Split complex equations into real and imaginary parts.
  # This forces coefficients of compact generators to be real.
  mR := List(mC, SplitQIList);

  # Real nullspace.
  sol := NullspaceMat(mR);

  # Stabilizer generators inside the compact real form.
  stab := List(sol, c -> LinearCombination(kB, c));

  return rec(
    compact_basis := kB,
    coefficient_basis := sol,
    stabilizer_generators := stab
  );
end;;

ScalarOnVectorInBasis := function(bV, w, cw)
  local wc, cwc, i, lam;

  wc := Coefficients(bV, w);
  cwc := Coefficients(bV, cw);

  lam := fail;

  for i in [1..Length(wc)] do
    if wc[i] <> 0 then
      lam := cwc[i] / wc[i];
      break;
    fi;
  od;

  if lam = fail then
    return fail;
  fi;

  # Sanity check: central action should act by a scalar on an irreducible piece.
  if cwc <> lam * wc then
    Print("Warning: vector is not an eigenvector for this center element.\n");
  fi;

  return lam;
end;;

AnalyzeStabilizerWithSLA := function(v, g, V)
  local stabData, h, k, z, W, pieces, i, zbas, hwv, charges, bV;

  bV := Basis(V);

  # Compact real stabilizer.
  stabData := CompactStabilizerAlgebra(v, g, V);

  # Complexification of compact stabilizer.
  # This is what SLA wants for Lie algebra type / highest weights.
  h := Subalgebra(g, stabData.stabilizer_generators);

  # Semisimple part and center.
  k := LieDerivedSubalgebra(h);
  z := LieCentre(h);

  Print("\n");
  Print("============================================\n");
  Print("Compact stabilizer data\n");
  Print("============================================\n");

  Print("Dimension of compact stabilizer = ",
        Length(stabData.stabilizer_generators), "\n");

  Print("Dimension of complexified stabilizer = ",
        Dimension(h), "\n");

  if Dimension(k) > 0 then
    Print("Semisimple type = ", SemiSimpleType(k), "\n");
  else
    Print("Semisimple type = none\n");
  fi;

  Print("Center dimension = ", Dimension(z), "\n\n");

  Print("Compact stabilizer coefficient basis relative to compact su(N) basis:\n");
  Print(stabData.coefficient_basis, "\n\n");

  Print("Compact stabilizer generators:\n");
  Print(stabData.stabilizer_generators, "\n\n");

  if Dimension(k) = 0 then
    Print("No semisimple part, so there are no nontrivial highest weights.\n");

    return rec(
      compact_stabilizer_data := stabData,
      complex_stabilizer := h,
      semisimple_part := k,
      center := z,
      pieces := []
    );
  fi;

  # Restrict V to the semisimple part of the stabilizer.
  W := ModuleByRestriction(V, k);
  pieces := DirectSumDecomposition(W);

  zbas := BasisVectors(Basis(z));

  Print("============================================\n");
  Print("Branching under semisimple stabilizer\n");
  Print("============================================\n\n");

  for i in [1..Length(pieces)] do
    hwv := HighestWeightVector(pieces[i]);

    charges := List(
      zbas,
      c -> ScalarOnVectorInBasis(bV, hwv, c^hwv)
    );

    Print("Piece ", i, ":\n");
    Print("  dimension = ", Dimension(pieces[i]), "\n");
    Print("  highest weight = ", HighestWeight(pieces[i]), "\n");
    Print("  center charges = ", charges, "\n");
    Print("  highest-weight vector = ", hwv, "\n\n");
  od;

  return rec(
    compact_stabilizer_data := stabData,
    complex_stabilizer := h,
    semisimple_part := k,
    center := z,
    restricted_module := W,
    pieces := pieces
  );
end;;

# ============================================================
# Example usage
# ============================================================

N := 8;;

g := SimpleLieAlgebra("A", N-1, CF(4));;

# Example: adjoint representation of su(7)_C = sl_7(C).
V := HighestWeightModule(g, [1,0,0,0,0,0,1]);;

bV := Basis(V);;

# Choose a vector in the representation.
v := bV[1];;

data := AnalyzeStabilizerWithSLA(v, g, V);;
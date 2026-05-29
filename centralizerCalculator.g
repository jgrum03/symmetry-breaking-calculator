LoadPackage("sla");

algebra := ["A", 2];;
highestWeight := [1,1];;
stabilizedVectorLabel := [0,0,0,-1,2,0,0,0];;


StabilizerAlgebra := function(v, g, V)
  local bV, kB, m, sol, stab;

  bV := Basis(V);
  kB := Basis(g);

  m := List(kB, x -> Coefficients(bV, x^v));

  sol := NullspaceMat(m);

  stab := List(sol, c -> LinearCombination(kB, c));

  return Subalgebra(g, stab);
end;;

g := SimpleLieAlgebra(algebra[1], algebra[2], Rationals);;
V := HighestWeightModule(g, highestWeight);;
bg := Basis(g);;
bv := Basis(V);;

stabilizedVector := LinearCombination(bv, stabilizedVectorLabel);;

stab := StabilizerAlgebra(stabilizedVector, g, V);;

levi := LeviMalcevDecomposition(stab)[1];;

ideals := DirectSumDecomposition(levi);;
ss := Filtered(ideals, K -> not IsLieSolvable(K));;

oplusCharacter := Encode(Unicode("&#x2295;", "XML"));;
timesCharacter := Encode(Unicode("&#x00D7;", "XML"));;

if Length(ss) = 0 then
    Print("The centralizer is trivial.");
else
    Print("The centralizer is ", SemiSimpleType(levi), ".\n");
fi;;

Print("Analysis of Representation of the Centralizer:\n==============================\n");
for i in [1..Length(ss)] do
    K := ss[i];
    Print(i, ":\nSubalgebra type: ", SemiSimpleType(K), "\n");
    branch := Branching(g, K, highestWeight);;
    if SemiSimpleType(K) = "A1" then
        repDimensions := branch[1]+1;
        mult := branch[2];
        Print("su(2) Rep: ", repDimensions[1][1], "^",mult[1]);
        for i in [2..Length(repDimensions)] do
            Print(oplusCharacter, repDimensions[i][1], "^", mult[i]);
        od;
        Print("\n");
    else
        Print("Highest weights: ");
        Print(branch[2][i], timesCharacter, branch[1][i]);
        for i in [2..Length(branch[1])] do
            Print(oplusCharacter, branch[2][i], timesCharacter, branch[1][i]);
        od;
    fi;
    Print("==============================\n");
od;
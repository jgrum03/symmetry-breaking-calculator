LoadPackage("sla");

algebra := ["C", 3];;

g := SimpleLieAlgebra(algebra[1], algebra[2], Rationals);;
bg := Basis(g);;

oplusCharacter := Encode(Unicode("&#x2295;", "XML"));;
timesCharacter := Encode(Unicode("&#x00D7;", "XML"));;

if algebra[1] = "A" then
    rep := List([1..algebra[2]], i -> 0);;;
    rep[1]:=1;;
    rep[Length(rep)]:=1;;
elif algebra[1] = "B" then
    rep := List([1..algebra[2]], i -> 0);;
    rep[2]:=1;;
elif algebra[1] = "C" then
    rep := List([1..algebra[2]], i -> 0);;
    rep[1]:=2;;
elif algebra[1] = "D" then
    rep := List([1..algebra[2]], i -> 0);;
    rep[2]:=1;;
elif algebra = ["E",6] then
    rep := [0,0,0,0,0,1];;
elif algebra = ["E",7] then
    rep := [0,0,0,0,0,0,1];;
elif algebra = ["E",8] then
    rep := [1,0,0,0,0,0,0,0];;
fi;

branchCatch := function(g, K, rep)
local result;
    BreakOnError := false;
    result := CALL_WITH_CATCH(Branching, [ g, K, rep ])[1];;
    BreakOnError := true;
    return result;
end;

StabilizerAlgebra := function(v, g)
  local basis, m, sol, stab;

  basis := Basis(g);

  m := List(basis, x -> Coefficients(basis, x*v));

  sol := NullspaceMat(m);

  stab := List(sol, c -> LinearCombination(basis, c));

  return Subalgebra(g, stab);
end;;

AnalyzeStabilizer := function(v, g)
    local stab, levi, ideals, ss, branch, repDimensions, mult, i, K, j;
    stab := StabilizerAlgebra(v, g);;

    levi := LeviMalcevDecomposition(stab)[1];;

    ideals := DirectSumDecomposition(levi);;
    ss := Filtered(ideals, K -> not IsLieSolvable(K));;
    if Length(ss) = 0 then
        Print("The centralizer is trivial.\n\n==============================\n");
    else
        Print("The centralizer is ", SemiSimpleType(levi), ".\n");
        Print("Analysis of Representation of the Centralizer:\n\n==============================\n\n");
        for i in [1..Length(ss)] do
            K := ss[i];
            Print(i, ":\nSubalgebra type: ", SemiSimpleType(K), "\n");
            # Print(K, "\n");
            if branchCatch(g, K, rep) then
                branch := Branching(g, K, rep);
                if SemiSimpleType(K) = "A1" then
                    repDimensions := branch[1]+1;
                    mult := branch[2];
                    Print("su(2) Rep: ", repDimensions[1][1], "^",mult[1]);
                    for j in [2..Length(repDimensions)] do
                        Print(oplusCharacter, repDimensions[j][1], "^", mult[j]);
                    od;
                else
                    Print("Highest weights: ");
                    Print(branch[2][1], timesCharacter, branch[1][1]);
                    for j in [2..Length(branch[1])] do
                        Print(oplusCharacter, branch[2][j], timesCharacter, branch[1][j]);
                    od;
                fi;
            fi;
            Print("\n\n==============================\n\n");
        od;
    fi;;
end;;

g := SimpleLieAlgebra(algebra[1], algebra[2], Rationals);;
bg := Basis(g);;

oplusCharacter := Encode(Unicode("&#x2295;", "XML"));;
timesCharacter := Encode(Unicode("&#x00D7;", "XML"));;

orbs := NilpotentOrbits(g);;
for o in orbs do
    stabilizedVector := SL2Triple(o)[3];;
    Print("Stabilizer of ", stabilizedVector, ":\n");;
    AnalyzeStabilizer(stabilizedVector, g);;
    Print("\n");;
od;;
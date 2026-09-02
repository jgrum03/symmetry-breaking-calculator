LoadPackage("sla");

algebra := ["E", 8];;

g := SimpleLieAlgebra(algebra[1], algebra[2], CF(4));;
bg := Basis(g);;

oplusCharacter := Encode(Unicode("&#x2295;", "XML"));;
timesCharacter := Encode(Unicode("&#x00D7;", "XML"));;
I := E(4);;

filename := Concatenation("AdjCentralizer_", algebra[1], String(algebra[2]), "_1_Nil.csv");;

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
    # NOTE: I don't know if I did the correct thing for the exceptionals; I haven't tested them yet.
elif algebra = ["E",6] then
    rep := [0,0,0,0,0,1];;
elif algebra = ["E",7] then
    rep := [0,0,0,0,0,0,1];;
elif algebra = ["E",8] then
    rep := [0,0,0,0,0,0,0,1];;
fi;

branchCatch := function(g, K, rep)
local result;
    BreakOnError := false;
    result := CALL_WITH_CATCH(Branching, [ g, K, rep ])[1];;
    BreakOnError := true;
    return result;
end;

# Added code created by Claude to align the Cartan subalgebra of the centralizer with that of the original algebra.
AlignCartanSubalgebra := function(g, K)
    local hg, hK, typeStr, rk;
    hg := CartanSubalgebra(g);;
    hK := Intersection(hg, K);;
    typeStr := SemiSimpleType(K);;
    rk := Int(typeStr{[2..Length(typeStr)]});;   # strip leading type letter, parse rank
    if Dimension(hK) <> rk then
        Error("h_g \\cap K has dimension ", Dimension(hK),
              " but rank(", typeStr, ") = ", rk,
              " -- CSA misaligned, needs a different fix for this orbit.");
    fi;
    SetCartanSubalgebra(K, Subalgebra(K, BasisVectors(Basis(hK))));;
    return K;
end;;

StabilizerAlgebra := function(v, g)
  local basis, m, sol, stab;

  basis := Basis(g);

  m := List(basis, x -> Coefficients(basis, x*v));

  sol := NullspaceMat(m);

  stab := List(sol, c -> LinearCombination(basis, c));

  return Subalgebra(g, stab);
end;;

AnalyzeStabilizer := function(v, g)
    local stab, levi, ideals, ss, branch, repDimensions, mult, i, K, j, type, out, tempString;

    out := [String(v)];
    stab := StabilizerAlgebra(v, g);;

    levi := LeviMalcevDecomposition(stab)[1];;

    ideals := DirectSumDecomposition(levi);;
    ss := Filtered(ideals, K -> not IsLieSolvable(K));;
    if Length(ss) = 0 then
        Print("The centralizer is trivial.\n\n==============================\n");
        Add(out, "0",1);;
        Add(out, "0");;
    else
        Print("The centralizer is ", SemiSimpleType(levi), ".\n");
        Add(out,String(SemiSimpleType(levi)),1);;
        Print("Analysis of Representation of the Centralizer:\n\n==============================\n\n");
        for i in [1..Length(ss)] do
            K := ss[i];
            AlignCartanSubalgebra(g, K);;
            type := SemiSimpleType(K);
            Print(i, ":\nSubalgebra type: ", type, "\n");
            Add(out, type);;
            # Print(K, "\n");
            Print(Branching(g, K, rep), "\n");
            if branchCatch(g, K, rep) then
                branch := Branching(g, K, rep);
                if type = "A1" then
                    repDimensions := branch[1]+1;
                    mult := branch[2];
                    Print("su(2) Rep: ", repDimensions[1][1], "^",mult[1]);
                    tempString := Concatenation("\"",String(repDimensions[1][1]),"^",String(mult[1]));
                    for j in [2..Length(repDimensions)] do
                        Print(oplusCharacter, repDimensions[j][1], "^", mult[j]);
                        tempString := Concatenation(tempString, "+", String(repDimensions[j][1]), "^", String(mult[j]));
                    od;
                    # Print("\n\n");
                    # Print("Orbit partition: ", OrbitPartition(o), "\n");
                    # Print("branch[1] (raw): ", branch[1], "\n");
                    # Print("branch[2] (raw): ", branch[2], "\n\n");
                else
                    Print("Highest weights: ");
                    Print(branch[2][1], timesCharacter, branch[1][1]);
                    tempString := Concatenation("\"", String(branch[2][1]), "x", String(branch[1][1]));
                    for j in [2..Length(branch[1])] do
                        Print(oplusCharacter, branch[2][j], timesCharacter, branch[1][j]);
                        tempString := Concatenation(tempString, "+", String(branch[2][j]), "x", String(branch[1][j]));
                    od;
                fi;
                tempString := Concatenation(tempString, "\"");;
                Add(out, tempString);;
            fi;
            Print("\n\n==============================\n\n");
        od;
    fi;;
    return out;
end;;

# SAVING A FILE:
PrintTo(filename, "Unbroken Algebra,Stabilized Vector,Ideal,Rep,Repeat\n");;
orbs := NilpotentOrbits(g);;
for o in orbs do
    stabilizedVector := SL2Triple(o)[3];;

    Print("Stabilizer of ", stabilizedVector, ":\n");;
    temp := AnalyzeStabilizer(stabilizedVector, g);;
    AppendTo(filename, JoinStringsWithSeparator(temp, ","), "\n");;
    Print("\n");;
od;;

FundamentalMatrix := function(x)
    local V, bV, fundRep;
    fundRep :=List([1..algebra[2]], i -> 0);
    fundRep[1]:=1;
    V := HighestWeightModule(g, fundRep);
    bV := Basis(V);

    # Usual column convention: column j is x acting on basis vector j
    return TransposedMat(List(bV, v -> Coefficients(bV, x^(v))));
end;;

FindInvariantForm := function(g, basis)
    local gens, n, eqs, row, M, i, k, a, b, sol, J;
    
    gens := List(basis, x -> FundamentalMatrix(x));
    n := Length(gens[1]);
    
    # For each generator M and each (a,b), the condition M^T J + J M = 0
    # gives sum_{c} (M[c][a] J[c][b] + J[a][c] M[c][b]) = 0
    # This is a linear system in the n^2 entries of J, written as a vector
    # with index (a-1)*n + b
    
    eqs := [];
    for M in gens do
        for a in [1..n] do
            for b in [1..n] do
                row := ListWithIdenticalEntries(n^2, 0);
                for k in [1..n] do
                    # From M^T J: M[k][a] * J[k][b]
                    row[(k-1)*n + b] := row[(k-1)*n + b] + M[k][a];
                    # From J M: J[a][k] * M[k][b]
                    row[(a-1)*n + k] := row[(a-1)*n + k] + M[k][b];
                od;
                Add(eqs, row);
            od;
        od;
    od;
    
    sol := NullspaceMat(TransposedMat(eqs));
    Print("Dimension of solution space: ", Length(sol), "\n");
    
    # Reshape each solution vector into an n x n matrix
    return List(sol, v -> List([1..n], a -> v{[(a-1)*n+1..a*n]}));
end;;

RealCompactFormBasis := function(g)
    local basis, chevBasis, newH, imagE, realE;
    
    chevBasis := ChevalleyBasis(g);
    newH := chevBasis[3] * I;
    realE := chevBasis[1] - chevBasis[2];
    imagE := (chevBasis[1] + chevBasis[2]) * I;
    basis := Concatenation([newH, realE, imagE]);
    return basis;
end;;
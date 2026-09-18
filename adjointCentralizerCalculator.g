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

StabilizerAlgebra := function(v, g)
  local basis, m, sol, stab;

  basis := Basis(g);

  m := List(basis, x -> Coefficients(basis, x*v));

  sol := NullspaceMat(m);

  stab := List(sol, c -> LinearCombination(basis, c));

  return Subalgebra(g, stab);
end;;

##########################################################################
##  utilities
##########################################################################

SafeCall := function(fn, args)
    local r;
    BreakOnError := false;
    r := CALL_WITH_CATCH(fn, args);;
    BreakOnError := true;
    return r;
end;;

##  z(e) cap z(f) -- reductive by Jacobson-Morozov, no Levi needed
ReductiveCentralizer := function(g, e, f)
    local S;
    S := Intersection(StabilizerAlgebra(e, g), StabilizerAlgebra(f, g));;
    return Subalgebra(g, BasisVectors(Basis(S)));
end;;

##  simple coroots of K, with a structural validity check on K's own CSA
SimpleCoroots := function(K)
    local R, h, nroots;
    R := RootSystem(K);;
    if R = fail then Error("K has no root system"); fi;
    h := CanonicalGenerators(R)[3];;
    nroots := 2*Length(PositiveRoots(R)) + Length(h);;
    if nroots <> Dimension(K) then
        Error("root system accounts for ", nroots, " dimensions but dim K = ",
              Dimension(K), " -- K's Cartan subalgebra is not full rank");
    fi;
    return h;
end;;

##########################################################################
##  weights of g under K, in Dynkin labels -- no projection required
##########################################################################

JointWeights := function(g, hlist)
    local B, n, F, id, spaces, h, A, ns, new, S, lam, inter;
    B  := Basis(g);;   n := Dimension(g);;   F := LeftActingDomain(g);;
    id := IdentityMat(n, F);;
    spaces := [ [ [], IdentityMat(n, F) ] ];      # [ partial label tuple, row basis ]
    for h in hlist do
        A   := AdjointMatrix(B, h);;
        new := [];;
        for lam in Set(Eigenvalues(F, A)) do
            ns := NullspaceMat(A - lam*id);;
            if Length(ns) > 0 then
                for S in spaces do
                    inter := SumIntersectionMat(S[2], ns)[2];;
                    if Length(inter) > 0 then
                        Add(new, [ Concatenation(S[1], [lam]), inter ]);
                    fi;
                od;
            fi;
        od;
        spaces := new;;
    od;
    return List(spaces, S -> [ S[1], Length(S[2]) ]);
end;;

##  peel irreducibles off the weight multiset, maximal-first
PeelHighestWeights := function(K, wts)
    local dom, lams, mult, dc, i, j, k, pos, m, chosen, isMax, result;

    dom  := Filtered(wts, w -> ForAll(w[1], c -> c >= 0));;
    lams := List(dom, w -> w[1]);;
    mult := List(dom, w -> w[2]);;
    dc   := List(lams, l -> DominantCharacter(K, l));;

    result := [];;
    while ForAny(mult, m -> m > 0) do
        chosen := fail;;
        for i in [1..Length(lams)] do
            if mult[i] > 0 then
                isMax := true;;
                for j in [1..Length(lams)] do
                    if j <> i and mult[j] > 0 and lams[i] in dc[j][1] then
                        isMax := false;; break;
                    fi;
                od;
                if isMax then chosen := i;; break; fi;
            fi;
        od;
        if chosen = fail then Error("no maximal weight -- inconsistent data"); fi;

        m := mult[chosen];;
        Add(result, [ lams[chosen], m ]);
        for k in [1..Length(dc[chosen][1])] do
            pos := Position(lams, dc[chosen][1][k]);;
            if pos <> fail then
                mult[pos] := mult[pos] - m*dc[chosen][2][k];;
                if mult[pos] < 0 then
                    Error("negative multiplicity at ", lams[pos]);
                fi;
            fi;
        od;
    od;
    return result;
end;;

DecomposeUnder := function(g, K)
    local h, wts, bad, result, total;
    h   := SimpleCoroots(K);;
    wts := JointWeights(g, h);;

    bad := Filtered(wts, w -> not ForAll(w[1], c -> IsInt(c)));;
    if Length(bad) > 0 then
        Error("non-integral weights: ", List(bad, w -> w[1]));
    fi;
    if Sum(wts, w -> w[2]) <> Dimension(g) then
        Error("weights sum to ", Sum(wts, w -> w[2]), " not ", Dimension(g));
    fi;

    result := PeelHighestWeights(K, wts);;
    total  := Sum(result, r -> r[2]*DimensionOfHighestWeightModule(K, r[1]));;
    if total <> Dimension(g) then
        Error("dimensions do not close: ", total, " vs ", Dimension(g));
    fi;
    SortBy(result, r -> -DimensionOfHighestWeightModule(K, r[1]));
    return result;
end;;

##########################################################################
##  per-orbit analysis -- CSV columns unchanged
##########################################################################

AnalyzeStabilizer := function(e, f, g)
    local L, Lss, ideals, ss, i, j, K, type, dec, ok, out, tempString;

    out := [String(e)];;
    L   := ReductiveCentralizer(g, e, f);;
    ideals := DirectSumDecomposition(L);;
    ss  := Filtered(ideals, K -> not IsLieSolvable(K));;

    if Length(ss) = 0 then
        Print("The centralizer is toral or trivial (dim ", Dimension(L), ").\n");
        Print("\n==============================\n");
        Add(out, "0", 1);;  Add(out, "0");;
        return out;
    fi;

    Lss := LieDerivedSubalgebra(L);;
    Print("The centralizer is ", SemiSimpleType(Lss),
          " plus ", Dimension(L) - Dimension(Lss), "-dim center.\n");
    Add(out, String(SemiSimpleType(Lss)), 1);;
    Print("Analysis of Representation of the Centralizer:\n\n",
          "==============================\n\n");

    for i in [1..Length(ss)] do
        K    := ss[i];;                       # untouched: valid CSA already
        type := SemiSimpleType(K);;
        Print(i, ":\nSubalgebra type: ", type, "\n");
        Add(out, type);;

        ok := SafeCall(DecomposeUnder, [g, K]);;
        if ok[1] = false then
            Print("Decomposition failed for this subalgebra.\n");
            Add(out, "\"DECOMPOSITION_FAILED\"");;
        else
            dec := ok[2];;
            tempString := "\"";
            if type = "A1" then
                Print("su(2) Rep: ");
                for j in [1..Length(dec)] do
                    if j > 1 then
                        Print(oplusCharacter);
                        tempString := Concatenation(tempString, "+");
                    fi;
                    Print(dec[j][1][1]+1, "^", dec[j][2]);
                    tempString := Concatenation(tempString,
                        String(dec[j][1][1]+1), "^", String(dec[j][2]));
                od;
            else
                Print("Highest weights: ");
                for j in [1..Length(dec)] do
                    if j > 1 then
                        Print(oplusCharacter);
                        tempString := Concatenation(tempString, "+");
                    fi;
                    Print(dec[j][2], timesCharacter, dec[j][1]);
                    tempString := Concatenation(tempString,
                        String(dec[j][2]), "x", String(dec[j][1]));
                od;
            fi;
            Add(out, Concatenation(tempString, "\""));;
        fi;
        Print("\n\n==============================\n\n");
    od;
    return out;
end;;

##########################################################################
##  main loop
##########################################################################

PrintTo(filename, "Unbroken Algebra,Stabilized Vector,Ideal,Rep,Repeat\n");;
orbs := NilpotentOrbits(g);;
for o in orbs do
    triple := SL2Triple(o);;                  # [ f, h, e ]
    Print("Stabilizer of ", triple[3], ":\n");;
    temp := AnalyzeStabilizer(triple[3], triple[1], g);;
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
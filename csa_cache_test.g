###########################################################################
##  csa_cache_test.g -- when does GAP populate CartanSubalgebra?
###########################################################################

Report := function(label, L)
    Print(String(label, -32), " HasCartanSubalgebra = ",
          HasCartanSubalgebra(L), "\n");
end;;

##  Test 0: does the attribute cache at all? ###############################
##  If this prints false/true, caching is real. If false/false, there is
##  no caching and the whole write-once theory is moot.
Test0 := function(makeFresh)
    local L;
    L := makeFresh();;
    Print("--- Test 0: caching happens at all ---\n");
    Print("before CartanSubalgebra call: ", HasCartanSubalgebra(L), "\n");
    CartanSubalgebra(L);;
    Print("after  CartanSubalgebra call: ", HasCartanSubalgebra(L), "\n\n");
end;;

##  Test 1: is it set at construction time? ################################
Test1 := function(g)
    local bg, sub, ideals, i;
    bg := BasisVectors(Basis(g));;
    Print("--- Test 1: state immediately after construction ---\n");
    Report("parent algebra as built", g);
    sub := Subalgebra(g, bg{[1, 2]});;
    Report("Subalgebra(g, gens)", sub);
    sub := SubalgebraNC(g, bg{[1, 2]});;
    Report("SubalgebraNC(g, gens)", sub);
    Print("\n");
end;;

##  Test 2: which operations trigger it? ###################################
##  Each probe gets a FRESH object, since once triggered it stays triggered.
Probe := function(makeFresh, opname, op)
    local L, before, call, after;
    L      := makeFresh();;
    before := HasCartanSubalgebra(L);;
    call   := CALL_WITH_CATCH(op, [L]);;
    after  := HasCartanSubalgebra(L);;
    Print(String(opname, -26),
          " before=", String(before, -6),
          " after=",  String(after, -6),
          " TRIGGERED=", String(after and not before, -6),
          " op_ok=", call[1], "\n");
end;;

Test2 := function(makeFresh)
    local probes, p;
    Print("--- Test 2: which operations populate the slot ---\n");
    probes := [
      [ "Dimension",               Dimension               ],
      [ "Basis",                   Basis                   ],
      [ "String (ViewObj path)",   String                  ],
      [ "IsLieSolvable",           IsLieSolvable           ],
      [ "IsLieNilpotent",          IsLieNilpotent          ],
      [ "LieDerivedSubalgebra",    LieDerivedSubalgebra    ],
      [ "DirectSumDecomposition",  DirectSumDecomposition  ],
      [ "SemiSimpleType",          SemiSimpleType          ],
      [ "RootSystem",              RootSystem              ],
      [ "ChevalleyBasis",          ChevalleyBasis          ],
      [ "LeviMalcevDecomposition", LeviMalcevDecomposition ]
    ];;
    for p in probes do
        Probe(makeFresh, p[1], p[2]);
    od;
    Print("\n");
end;;

##  Test 3: overwrite semantics ############################################
Test3 := function(makeFresh)
    local L, bl, H1, H2, call, v;
    Print("--- Test 3a: set twice on a virgin object ---\n");
    L  := makeFresh();;
    bl := BasisVectors(Basis(L));;
    H1 := Subalgebra(L, [bl[1]]);;
    H2 := Subalgebra(L, [bl[2]]);;
    SetCartanSubalgebra(L, H1);;
    Print("after set#1, equals H1? ", CartanSubalgebra(L) = H1, "\n");
    call := CALL_WITH_CATCH(SetCartanSubalgebra, [L, H2]);;
    v    := CartanSubalgebra(L);;
    Print("set#2 raised error?     ", not call[1], "\n");
    Print("now equals H2?          ", v = H2, "\n");
    Print("still equals H1?        ", v = H1, "\n\n");

    Print("--- Test 3b: set AFTER auto-computation (the real case) ---\n");
    L  := makeFresh();;
    SemiSimpleType(L);;                        # provoke the auto-compute
    Print("slot populated by SemiSimpleType? ", HasCartanSubalgebra(L), "\n");
    bl := BasisVectors(Basis(L));;
    H1 := Subalgebra(L, [bl[1]]);;
    call := CALL_WITH_CATCH(SetCartanSubalgebra, [L, H1]);;
    Print("set raised error?       ", not call[1], "\n");
    Print("took our value?         ", CartanSubalgebra(L) = H1, "\n\n");
end;;

##  Driver -- run on something small first ##################################
g     := SimpleLieAlgebra("A", 3, Rationals);;
mkFresh := function() return Subalgebra(g, BasisVectors(Basis(g))); end;;

Test0(mkFresh);
Test1(g);
Test2(mkFresh);
Test3(mkFresh);
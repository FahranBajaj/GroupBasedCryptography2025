# f:="C:/Users/WHERLEYWS21/tester.g";
# Read(f);

N_LETTERS := 10; # was 4
G := SymmetricGroup(N_LETTERS);
CONJUGATION_ACTION := OnPoints; # action is conjugation

FindAllConjugators := function(G, g, h)
    centralizer := Centralizer(G, g); # centralizer of g
    r := RepresentativeAction(G, g, h, CONJUGATION_ACTION); # 
    return RightCoset(centralizer, r);
end;

printMe := function()
    conjugacyClasses := ConjugacyClasses(G);
    for conjugacyClass in conjugacyClasses do
        for g in Elements(conjugacyClass) do 
            for h in Elements(conjugacyClass) do 
                Print("g: ", g, "\nh: ", h, "\nPossible conjugators: ", FindAllConjugators(G, g, h), "\n\n");
            od;
            Print("\n------------------------------------------------------------\n");
        od;
        Print("\n*************************************************************\n*************************************************************\n");
    od;
end;

Print("\n\n******************************************************************************************\n");
Print("\t\t\t\tTUPLES OF Gs & Hs");
Print("\n******************************************************************************************\n\n");


IntersectionOfTuples := function(TUPLE_LEN, s_what)
    Print("(Background info: length of tuples is ", TUPLE_LEN, " and the symmetric group is S", s_what, ".)\n\n");
    # TUPLE_LEN: length of tuples of g and h
    # s_what: which symmetric group number you want

    G := SymmetricGroup(s_what);
    # getting tuples of g and h values
    gTuple := [];
    hTuple := [];
    ghConjugators := [];

    # pick a random conjugator c
    c := Random(G);
    Print(c);
    Print("\n");

    for i in [1..TUPLE_LEN] do
        # make tuples of random g values
        gVal := Random(G);
        Append(gTuple, [gVal]);

        # make tuples of g^r for h values
        Append(hTuple, [gVal^c]);

        # all conjugators of a g/h pair
        allConj := FindAllConjugators(G,gVal,gVal^c);
        Append(ghConjugators, [Elements(allConj)]);

        Print("g: ", gTuple[i], " h: ", hTuple[i], " all reps: ", ghConjugators[i], "\n");
        Print("\n------------------------------------------------------------\n");
    od;

    # finding the intersection of the tuples
    intersect := ghConjugators[1];

    for i in [1..Length(ghConjugators)] do
    intersect := Intersection(intersect, ghConjugators[i]);
    od;

    Print("\nIntersection of conjugators: ", intersect);
end;

IntersectionOfTuples(4,5);
N_LETTERS := 4;
G := SymmetricGroup(N_LETTERS);
CONJUGATION_ACTION := OnPoints;

FindAllConjugators := function(G, g, h)
    centralizer := Centralizer(G, g);
    r := RepresentativeAction(G, g, h, CONJUGATION_ACTION);
    return RightCoset(centralizer, r);
end;

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

N_LETTERS := 20;
G := SymmetricGroup(N_LETTERS);
CONJUGATION_ACTION := OnPoints; 
NUM_TRIALS := 10000;
NUM_PAIRS := 2;

FindAllConjugators := function(G, g, h)
    local centralizer, r;
    centralizer := Centralizer(G, g); 
    r := RepresentativeAction(G, g, h, CONJUGATION_ACTION); 
    return Elements(RightCoset(centralizer, r));
end;

LengthOfIntersection := function()
    local possibleConjugators, r, i, g, h, allConj;
    r := Random(G);
    g := Random(G);
    h := g^r;
    possibleConjugators := FindAllConjugators(G, g, h);

    for i in [2..NUM_PAIRS] do
        g := Random(G);
        h := g^r;
        allConj := FindAllConjugators(G, g, h);
        possibleConjugators := Intersection(possibleConjugators, allConj);
    od;
    return Length(possibleConjugators);
end;

lengths := [];
for trial in [1..NUM_TRIALS] do
    Append(lengths, [LengthOfIntersection()]);

    #I am impatient.
    if trial mod QuoInt(NUM_TRIALS, 10) = 0 then 
        Print("Done with ", trial, " trials.\n");
    fi;
od;
PrintTo("./.output", lengths);
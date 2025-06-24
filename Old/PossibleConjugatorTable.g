N_LETTERS := 5;
G := SymmetricGroup(N_LETTERS);
CONJUGATION_ACTION := OnPoints;

FindAllConjugators := function(G, g, h)
    local centralizer, r;
    centralizer := Centralizer(G, g);
    r := RepresentativeAction(G, g, h, CONJUGATION_ACTION);
    return RightCoset(centralizer, r);
end;

conjugacyClasses := ConjugacyClasses(G);
allPossibleConjugators := NewDictionary([(1, 2), (1, 2)], true);
#Lines that print the table of all possible conjugators are commented out.
for conjugacyClass in conjugacyClasses do
    for g in Elements(conjugacyClass) do 
        for h in Elements(conjugacyClass) do 
            possibleConjugators := FindAllConjugators(G, g, h);
            AddDictionary(allPossibleConjugators, [g, h], possibleConjugators);
            #Print("g: ", g, "\nh: ", h, "\nPossible conjugators: ", possibleConjugators, "\n\n");
        od;
        #Print("\n------------------------------------------------------------\n");
    od;
    #Print("\n*************************************************************\n*************************************************************\n");
od;


#For each pair of conjugacy tables, what is the maximum size of the intersection of two boxes?
conjugacyClasses := ConjugacyClasses(G);
for i in [2..Length(conjugacyClasses)] do #first conjugacy class is identity, which isn't interesting
    for j in [i..Length(conjugacyClasses)] do
        class1 := conjugacyClasses[i];
        class2 := conjugacyClasses[j];
        maxIntersectionSize := 0;
        maximalBoxes := [];
        for g1 in Elements(class1) do 
            for h1 in Elements(class1) do 
                box1 := LookupDictionary(allPossibleConjugators, [g1, h1]);
                for g2 in Elements(class2) do 
                    for h2 in Elements(class2) do 
                        #Want distinct pairs (g1, h1) and (g2, h2)
                        #Moreover, if g1 = g2 but h1 <> h2 or vice versa, then intersection will definitely be empty
                        if g1 <> g2 and h1 <> h2 then 
                            box2 := LookupDictionary(allPossibleConjugators, [g2, h2]);
                            possibleConjugators := Elements(Intersection(box1, box2));
                            if Length(possibleConjugators) > maxIntersectionSize then 
                                maxIntersectionSize := Length(possibleConjugators);
                                maximalBoxes := [[g1, h1, g2, h2]];
                            elif Length(possibleConjugators) = maxIntersectionSize then 
                                Append(maximalBoxes, [[g1, h1, g2, h2]]);
                            fi;
                        fi;
                    od;
                od;
            od;
        od;
        Print("Class 1 cycle structure: ", Representative(class1), "\nClass 2 cycle structure: ", Representative(class2), 
        "\nMaximal Intersection Size: ", maxIntersectionSize);
        if false then #Turn on if you want to see a choice of (g1, h1) and (g2, h2) that attain the maximum intersection size
            Print("\n\nA Box Attaining Max Intersection: \n");
            maximalBox := maximalBoxes[1];
            g1 := maximalBox[1];
            h1 := maximalBox[2];
            g2 := maximalBox[3];
            h2 := maximalBox[4];
            possibleConjugators := Elements(Intersection(LookupDictionary(allPossibleConjugators, [g1, h1]), LookupDictionary(allPossibleConjugators, [g2, h2])));
            Print("g1: ", g1, " h1: ", h1, " g2: ", g2, " h2: ", h2);
            Print("\nPossible Conjugators: ", possibleConjugators);
            fi;
        Print("\n------------------------------------------------------------\n");
    od;
od;

RandomElementList := function(len , group, list_size)
 
    local i , j, relations, rule, rules, rules_product, rules_equivalence, generators, family, randomelt, successors,
		gen, rws, letter_rep, starters, element_list;

    element_list := [];
   
    AG_UseRewritingSystem(group);
    relations := FindGroupRelations(group,2);

    relations := Filtered(relations, x -> (Length(Word(x)) <= 3) ); 

    if not relations = [] then
	    AG_AddRelators(group, relations);
    fi;

    rws        := AG_RewritingSystem(group);
    generators := GeneratorsOfMonoid(Image(rws!.mhom));
 
    rules      := AG_RewritingSystemRules(group);
    rules_product := [];
    rules_equivalence := [];
    family     := FamilyObj(Word(One(group)));

    for rule in rules do
	letter_rep := LetterRepAssocWord(rule[1]);
	if Size(letter_rep) = 2 then
		Add(rules_product, letter_rep);
        elif Size(letter_rep) = 1 then
		Add(rules_equivalence, [letter_rep[1], LetterRepAssocWord(rule[2])]);
	fi;
    od;

    starters   := Set([1..Size(generators)]);
    successors := List([1..Size(generators)], x -> Set([1..Size(generators)]) );
   
    # No generator can be followed by an element that will simplify the product 
    for rule in rules_product do
	RemoveSet(successors[rule[1]], rule[2]);
    od;

    # If two generators are equivalent, ignore one
    for rule in rules_equivalence do
	for i in [1..Size(successors)] do	
		RemoveSet(successors[i], rule[1]);
	od;
	successors[rule[1]] := [];
	RemoveSet(starters, rule[1]);
    od;

    for i in [1..list_size] do
	    gen :=  Random(starters);
	    randomelt := [gen];
	 
	    for j in [2..len] do  
		    gen := Random(successors[gen]);
		    Add( randomelt, gen );
	    od;

	    # Changes from denoting generators/inverses as 1, 2, 3.. to 1, -1, 2, -2..
	    randomelt := List( randomelt, x -> (-1)^(x + 1)*Ceil(Float(x/2)) );
	    randomelt := List( randomelt, x -> Int(x) );

	    randomelt := AssocWordByLetterRep(family, randomelt);
	    # TODO: Representative doesn't work
	    randomelt := Representative(randomelt, One(group));

	    Add(element_list, randomelt);
    od;

    return element_list;
 
end;

ElemWithPermutation := function(G, sigma)
    local generators, permGroup, homomorphism;
    generators := GeneratorsOfGroup(G);
    permGroup := PermGroupOnLevel(G, 1);
    homomorphism := GroupHomomorphismByImagesNC(G, permGroup, generators, List(generators, g -> PermOnLevel(g, 1)));
    return PreImagesRepresentative(homomorphism, sigma);
end;
 

# LIST EXTENSION
list_extension := function(G, listLen, wordLen)
    local new_gs, new_gs_perms, trivial_actions_gs, i, g, gP_inverse;

    new_gs := RandomElementList(wordLen, G, listLen);
    new_gs_perms := List(new_gs, x -> PermOnLevel(x,1));
    trivial_actions_gs := [];

    for i in [1..Length(new_gs)] do
        # get g and its perm's inverse
        g := new_gs[i];
        gP_inverse := new_gs_perms[i]^-1;

        # find the corresponding word in list
        trivial_actions_gs[i] := g*ElemWithPermutation(G, gP_inverse);
    od;

    return trivial_actions_gs;
end;

G := AutomatonGroup("a23 = (a23, 1, 1)(2, 3), a13 = (1, a13, 1)(1, 3), a12 = (1, 1, a12)(1, 2)"); #gr: hanoi 3

Print(list_extension(G,10,5));

Print("\n\n", ElemWithPermutation(G,(1,2,3)));
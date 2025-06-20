# Creates new g,h lists of length 50, with new elements multiples of number_of_factors factors of g's 	
LoadPackage("AutomGrp");
ExtendLists:=function(g_list, h_list, number_of_factors, listLen)
	local new_g_list, new_h_list, i, idxs, gs, hs;

	# number_of_factors := Int(Ceil(Float( key_length/Length(Word(g)) ))); 

	new_g_list := [];	
	new_h_list := [];	

	for i in [1..listLen] do
		idxs := List( [1..number_of_factors], x -> Random([1..Size(g_list)]) );
		gs := List(idxs, x -> g_list[x]);
		hs := List(idxs, x -> h_list[x]);
		Add(new_g_list, Product(gs));
		Add(new_h_list, Product(hs));	
	od;

	return [new_g_list, new_h_list];
end;

ElemWithPermutation := function(g_s, h_s, sigma)
    local G, H, permGroup, F, FGenerators, FToPerm, FToG, FToH, sigmaInF, g, h;
    G := Group(g_s);
    H := Group(h_s);
    permGroup := PermGroupOnLevel(G, 1);
    F := FreeGroup(Length(g_s));
    FGenerators := GeneratorsOfGroup(F);
    FToPerm := GroupHomomorphismByImagesNC(F, permGroup, FGenerators, List(g_s, g -> PermOnLevel(g, 1)));
    FToG := GroupHomomorphismByImagesNC(F, G, FGenerators, g_s);
    FToH := GroupHomomorphismByImagesNC(F, H, FGenerators, h_s);
    sigmaInF := PreImagesRepresentative(FToPerm, sigma);
    g := FToG(sigmaInF);
    h := FToH(sigmaInF);
    return [g, h];

end;
 

# LIST EXTENSION
list_extension := function(G, gs, hs, listLen, wordLen)
    local gh, new_gs, new_hs, new_gs_perms, trivial_actions_gs, trivial_actions_hs, i, g, h, gP_inverse, gh_output;

    gh := ExtendLists(gs, hs, wordLen, listLen);
    new_gs := gh[1];
    new_hs := gh[2];

    new_gs_perms := List(new_gs, x -> PermOnLevel(x,1));
    trivial_actions_gs := [];
    trivial_actions_hs := [];

    for i in [1..Length(new_gs)] do
        # get g and its perm's inverse
        g := new_gs[i];
        h := new_hs[i];
        gP_inverse := new_gs_perms[i]^-1;

        gh_output := ElemWithPermutation(gs, hs, gP_inverse);

        # find the corresponding word in list
        trivial_actions_gs[i] := g*gh_output[1];
        trivial_actions_hs[i] := h*gh_output[2];
    od;




    return [trivial_actions_gs, trivial_actions_hs];
end;

G := AutomatonGroup("a23 = (a23, 1, 1)(2, 3), a13 = (1, a13, 1)(1, 3), a12 = (1, 1, a12)(1, 2)"); #gr: hanoi 3
AG_UseRewritingSystem(G);
AG_UpdateRewritingSystem(G, 3);
gs := [a23*a12, a12*a13^-1];
r := a12;
hs := List(gs, x -> x^r);

Print(list_extension(G, gs, hs, 5, 5), "\n");

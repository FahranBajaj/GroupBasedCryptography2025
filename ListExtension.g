LoadPackage("AutomGrp");
ElemWithPermutation := function(G, sigma)
    local generators, permGroup, homomorphism;
    generators := GeneratorsOfGroup(G);
    permGroup := PermGroupOnLevel(G, 1);
    homomorphism := GroupHomomorphismByImagesNC(G, permGroup, generators, List(generators, g -> PermOnLevel(g, 1)));
    return PreImagesRepresentative(homomorphism, sigma);
end;

Bartholdi := AutomatonGroup("x=(1,1,1,1,1,1,1)(1,5)(3,7),    y=(1,1,1,1,1,1,1)(2,3)(6,7), z=(1,1,1,1,1,1,1)(4,6)(5,7), x1=(x1,x,1,1,1,1,1),    y1=(y1,y,1,1,1,1,1),    z1=(z1,z,1,1,1,1,1)");
word := ElemWithPermutation(Bartholdi, (1,7,2,3,4,6,5));
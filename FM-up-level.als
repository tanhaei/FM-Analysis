module FFM

sig Feature {}

sig Configuration {
	features: set Feature
}

one sig root, A, B, C extends Feature{}

sig c extends Configuration{}

pred Mandatory (c:Configuration, p:Feature, sf:set Feature)
{	p !in sf
	p in c.features => all f:sf | f in c.features
	p !in c.features => all f:sf | f !in c.features
}


pred Optional (c:Configuration, p:Feature, sf:set Feature)
{
	p !in sf
	p !in c.features => all f:sf | f !in c.features
}

pred AlternativeGroup (c:Configuration, p:Feature, sf:set Feature)
{
	p !in sf
	#sf >1
	p in c.features => one f:sf | f in c.features
	p !in c.features => all f:sf | f !in c.features
}

pred OrGroup (c:Configuration, p:Feature, sf:set Feature)
{
	p !in sf
	#sf >1
	p in c.features => some f:sf | f in c.features
	p !in c.features => all f:sf | f !in c.features
}

pred Requires (c:Configuration, f1:Feature, f2:Feature)
{
	f1 in c.features =>  f2 in c.features
}

pred Excludes (c:Configuration, f1:Feature, f2:Feature)
{
	f1 in c.features =>  f2 !in c.features
	f2 in c.features =>  f1 !in c.features
}

pred Removed (c:Configuration, sf:set Feature)
{
	all f:sf | f !in c.features
}


pred LHS (conf:Configuration)
{
	Optional[conf, root, A+B] 
	Optional[conf, A, C] 
}


pred RHS (conf:Configuration)
{
	Optional[conf, root, A+B+C] 
	Requires[conf, C, A] 
}

assert  BehaviorPreserved {
LHS[c] <=> RHS[c]
}
check BehaviorPreserved for 1



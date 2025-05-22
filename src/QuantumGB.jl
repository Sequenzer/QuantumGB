module QuantumGB

using Oscar;

greet() = print("Hello World!")

export 
    normal_form_noRedTail,
    normal_form_with_rep,
    interreduce!_noRedTail,
    get_obstruction_pairs,
    getQuantumRelationsByType,
    lm


include("ReductionAutomata.jl")
include("gbsteps.jl")
include("symmetric_group_gb.jl")
include("interactive_reduce.jl")
include("the_conjecture.jl")
include("parallelized_gbsteps.jl")
include("testing_functions.jl")
include("./general_proof/Lexicon.jl")
include("./general_proof/Term.jl")
include("./general_proof/utils.jl")
#include("cubep.jl")
#include("pointed_Bases.jl")


include("../examples/bg223t_data.jl")


end # module QuantumGB

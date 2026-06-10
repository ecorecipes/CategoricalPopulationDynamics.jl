module CategoricalPopulationDynamicsIndividualBasedExt

using CategoricalPopulationDynamics
using IndividualBasedPopulationDynamics
using LinearAlgebra: Diagonal, diag
import Random

"""
    lower(vnet::ValuedProjectionNet, target::IBMStageTarget)

Lower a stage-structured valued net to an individual-based (Ark ECS)
stage-structured continuous-time realization. Non-`fecundity` transition rates
become inter-stage movements (`Qtrans = U` with the diagonal dropped),
`fecundity`-tagged rates become the birth matrix (`B = F`), and `death` is the
per-stage mortality vector. Returns an Ark `World`; advance it with
`ibm_run_stage!` / `ibm_step_stage!`.
"""
function CategoricalPopulationDynamics.lower(
        vnet::CategoricalPopulationDynamics.ValuedProjectionNet,
        target::CategoricalPopulationDynamics.IBMStageTarget)
    U, F = CategoricalPopulationDynamics.survival_fecundity_matrices(vnet;
        fecundity = target.fecundity)
    n = size(U, 1)
    length(target.stages0) == n || throw(DimensionMismatch(
        "stages0 has length $(length(target.stages0)); expected $n stages"))
    Qtrans = U - Diagonal(diag(U))         # off-diagonal inter-stage movement rates
    birth = F                              # birth matrix B[to, from]
    death = target.death === nothing ? zeros(n) : collect(float.(target.death))
    length(death) == n || throw(DimensionMismatch(
        "death has length $(length(death)); expected $n stages"))
    stages0 = Int[]
    for (s, c) in enumerate(target.stages0)
        c > 0 && append!(stages0, fill(s, Int(c)))
    end
    rng = target.rng === nothing ? Random.default_rng() : target.rng
    return IndividualBasedPopulationDynamics.ibm_world_stage(Qtrans, death, birth;
        rng = rng, stages0 = stages0)
end

end # module

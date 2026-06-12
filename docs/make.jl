using Documenter
using CategoricalPopulationDynamics
using StructuredPopulationCore

# Headless plotting for runnable @example tutorials (GR).
ENV["GKSwstype"] = "100"

makedocs(;
    modules = [CategoricalPopulationDynamics, StructuredPopulationCore],
    warnonly = true,
    authors = "Simon Frost",
    sitename = "CategoricalPopulationDynamics.jl",
    format = Documenter.HTML(;
        prettyurls = get(ENV, "CI", "false") == "true",
        canonical = "https://ecorecipes.github.io/CategoricalPopulationDynamics.jl",
    ),
    pages = [
        "Home" => "index.md",
        "API Reference" => [
            "Schemas & Nets" => "api/schemas.md",
            "Domain Types" => "api/domains.md",
            "Kan Extensions" => "api/kan_extensions.md",
            "Stratification & Coarsening" => "api/stratification.md",
            "Diagnostics" => "api/diagnostics.md",
            "Composition" => "api/composition.md",
            "Valued Projection Nets" => "api/valued.md",
            "Lowering & Lifting" => "api/lowering.md",
            "Time-Lag Models" => "api/time_lag.md",
        ],
        "Tutorials" => [
            "Introduction to Categorical Projection Models" => "tutorials/01_introduction.md",
            "Kan Extensions and the IPM-MPM Adjunction" => "tutorials/02_kan_extensions.md",
            "Compositional Model Construction" => "tutorials/03_composition.md",
            "Stratification and Coarsening" => "tutorials/04_stratification_coarsening.md",
            "Lowering and Lifting: Connecting IPMs, MPMs, and Categorical Nets" => "tutorials/05_lowering_lifting.md",
            "Reconstructing a Published IPM from PADRINO" => "tutorials/06_padrino_reconstruction.md",
            "Decomposing a COMADRE Matrix Model: Loggerhead Sea Turtle Conservation" => "tutorials/07_comadre_reconstruction.md",
            "Valued Projection Nets" => "tutorials/08_valued_nets.md",
            "Environmental vs Demographic Stochasticity: A Categorical Perspective" => "tutorials/09_stochastic_deterministic.md",
            "Time-Lagged Categorical Projection Models" => "tutorials/10_time_lag.md",
            "Genotype Stratification: Bt Cotton Resistance Evolution" => "tutorials/11_bt_resistance_stratification.md",
            "Vector-Borne Disease Stratification" => "tutorials/12_xylella_epi_stratification.md",
            "Enemy Guild Composition" => "tutorials/13_whitefly_guild_composition.md",
            "Metapopulation Stratification" => "tutorials/14_lobesia_metapopulation.md",
            "Trophic Coarsening" => "tutorials/15_rice_fish_coarsening.md",
            "Continuous-State Organ Allocation" => "tutorials/16_cotton_organ_allocation.md",
            "Tritrophic Composition via Wiring Diagrams" => "tutorials/17_tritrophic_aphid_parasitoid.md",
            "Time-Lag Expansion and Diapause Stratification" => "tutorials/18_aedes_diapause_lag.md",
            "Continuous-State IPM with Spatial Stratification" => "tutorials/19_medfly_spatial_ipm.md",
            "Multi-Timescale Colony Dynamics" => "tutorials/20_bumblebee_nesting.md",
            "PBDM Supply–Demand via Timescale Nesting" => "tutorials/21_tritrophic_nesting.md",
            "Continuous-Time Stage Dynamics: Mosquito Development as a Generator" => "tutorials/22_mosquito_ctmc.md",
            "Continuous-Time Integral Projection: Perennial Herb Size Dynamics" => "tutorials/23_perennial_continuous_ipm.md",
            "Coupled Demographic Systems: Sterile Insect Technique as a ProjectionSystem" => "tutorials/24_coupled_sit_system.md",
            "Open Projection Nets: Structured Cospans and Pushout Composition" => "tutorials/25_open_nets_cospans.md",
            "Physiologically-Structured Populations: Advection, Mortality, and Boundary Influx" => "tutorials/26_pspm_size_structured.md",
            "Time Reparametrization Morphisms" => "tutorials/27_time_reparametrization.md",
            "Lowering to Individual-Based Models" => "tutorials/28_individual_based.md",
        ],
    ],
)

deploydocs(;
    repo = "github.com/ecorecipes/CategoricalPopulationDynamics.jl.git",
    push_preview = true,
)

using Documenter
using CategoricalProjectionModels
using ProjectionModels

makedocs(;
    modules = [CategoricalProjectionModels, ProjectionModels],
    warnonly = true,
    authors = "Simon Frost",
    sitename = "CategoricalProjectionModels.jl",
    format = Documenter.HTML(;
        prettyurls = get(ENV, "CI", "false") == "true",
        canonical = "https://ecorecipes.github.io/CategoricalProjectionModels.jl",
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
    ],
)

deploydocs(;
    repo = "github.com/ecorecipes/CategoricalProjectionModels.jl.git",
)

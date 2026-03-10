.PHONY: build mdgen html pdf clean all

PANDOC_FLAGS = --standalone --toc --mathjax \
    --css=style.css \
    --metadata title="Formal Verification of CategoricalProjectionModels.jl" \
    --metadata author="Simon Frost" \
    --highlight-style=tango

# Order matches CpmProofs.lean imports (dependency order)
MD_FILES = \
    StochCat.md Integration.md CondKernel.md KanBridge.md \
    Adjunction.md Dispersal.md KernelAlgebra.md \
    BinExample.md CompositeError.md MultiBin.md MarkovCat.md \
    TrapezoidalRule.md NonUniformPartition.md ProductBin.md BoxBin.md \
    SimpsonRule.md \
    MeasDet.md StochConvergence.md SpectralConvergence.md \
    EnvStochastic.md RandCategory.md \
    MonoidalStoch.md StochMarkov.md \
    StochSelfEnrichment.md WeightedColimit.md EnrichedKanExtension.md \
    EnrichedBridge.md Enriched.md

all: build mdgen html

# Build the Lean 4 project (verifies all proofs)
build:
	lake build

# Generate markdown from Lean source via mdgen
mdgen:
	rm -rf .mdgen_tmp
	mkdir -p .mdgen_tmp
	lake exe mdgen CpmProofs .mdgen_tmp
	cat $(addprefix .mdgen_tmp/, $(MD_FILES)) > CpmProofs.md
	rm -rf .mdgen_tmp
	@echo "Generated CpmProofs.md"

# Generate HTML from markdown
html: CpmProofs.md
	pandoc CpmProofs.md -o CpmProofs.html $(PANDOC_FLAGS)
	@echo "Generated CpmProofs.html"

# Generate PDF from markdown
pdf: CpmProofs.md
	pandoc CpmProofs.md -o CpmProofs.pdf \
	    --pdf-engine=lualatex \
	    --toc \
	    --metadata title="Formal Verification of CategoricalProjectionModels.jl" \
	    --metadata author="Simon Frost" \
	    --highlight-style=tango \
	    -H header.tex
	@echo "Generated CpmProofs.pdf"

clean:
	rm -f CpmProofs.html CpmProofs.pdf CpmProofs.md
	rm -rf .mdgen_tmp

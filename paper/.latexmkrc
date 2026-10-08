
# Turn off bibliography processing mode (equivalent to -bm=none)
$bibtex_use = 0;

# Override the biber command to do nothing
$biber = 'echo skipping biber';
$bibtex = 'echo skipping bibtex';

$pdf_mode = 1;
$pdflatex = 'pdflatex -synctex=1 -interaction=nonstopmode %O %S';

import camelot
tables = camelot.read_pdf("espagne_frontera_sur.pdf", pages="all", flavor="stream")
tables.export("output.csv", f="csv")
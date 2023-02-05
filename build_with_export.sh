echo "Exporting code from Isabelle (takes some minutes)"

( cd src/isabelle/ && ./export_code.sh )
cp src/isabelle/export/* src/verified_solver/export_isabelle

echo "Code export done"
./build.sh

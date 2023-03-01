echo "Exporting code from Isabelle (takes some minutes)"

./export_code.sh
cp -r export verified_solver/export_isabelle

echo "Code export done"
./build.sh

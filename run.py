import os


ocaml_exe_path = "_build/default/bin/main.exe"

print("Compiling OCaml module using dune")
res = os.system("dune build @all")
if res == 0:
    print("Compilation ran successfully")
else:
    print("Compilation ended with errors! exiting program!")
    exit(1)

print("Starting running tests: ")
root = input("Please enter the root dir: ")


failed_tests = []
for path, currentDirectory, files in os.walk(root):
    print(currentDirectory)
    for file in files:
        fpath = os.path.join(path, file)
        if "imports" in fpath:
            continue
        if "openzeppelin" in fpath:
            continue
        print(f'Running OCaml exe with file: {fpath}')
        res = os.system(f'{ocaml_exe_path} {fpath}')
        if "neg" in file:
            if res == 0:
                failed_tests.append(file)
        else:
            if res != 0:
                failed_tests.append(file)
        print(f'Failed tests: {len(failed_tests)}')
        for t in failed_tests:
            print(t)
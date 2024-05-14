#!/usr/bin/env python3
"""
This file locally checks if all files in the HepLean directory are imported correctly in 
the HepLean.lean file.
"""
import os
import re

directory = "./HepLean/"
files = []
for root, _, filenames in os.walk(directory):
    for filename in filenames:
        if filename.endswith(".lean"):
            files.append(os.path.join(root, filename))


with open("./HepLean.lean", 'r') as f:
    content = f.read()
    
imports = []
for line in content.split('\n'):
    match = re.match(r'import\s+(.*)', line)
    if match:
        imports.append(match.group(1))

files_as_imports = [] 
for file in files:
    file_name = file 
    file_name = file.replace("./", "").replace("/", ".").replace(".lean", "")
    files_as_imports.append(file_name)

files_as_imports.sort()
a = [0,3,2]

def file_check(imports, files_as_imports):
    fail = False 
    if imports != sorted(imports):
        print("The imports list is not sorted.")
        fail = True
    to_add = [] 
    for file in files_as_imports:
        if file not in imports:
            fail = True
            to_add.append(file)
    to_delete = []
    for file in imports:
        if file not in files_as_imports:
            fail = True
            to_delete.append(file)
    if len(to_add) != 0 : 
        print("The following files are not imported: ")
        for f in to_add:
            print(f)
    if len(to_delete) != 0 : 
        print("The following files should be deleted from HepLean.lean: ")
        for f in to_delete:
            print(f)
    if not fail:
        print("All files are imported correctly.")

print ("----- Local import check of files: ")
file_check(imports, files_as_imports)
print ("----- End of local import check of files ")
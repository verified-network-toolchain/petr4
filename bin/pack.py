from os import listdir, chdir, getcwd
import argparse
"""
1. Write python program to pack a directory into an ml file
   pack.py <dir> <file.ml>
   - argparse is a good module for this
   - print code to file.ml that initializes a map fs
     - [(key, val), (key', val')]
     - or other map data structures
   - visit every file in <dir>
     - store contents in fs[full path to file]
2. Implement P4pp.Eval.F signature for this data structure
3. Use P4pp.Eval.Make to create a preprocessor instance
4. replace P4pp.Eval.FileSystem with the new instance

"""

parser= argparse.ArgumentParser(description="Pack p4 files into an ml file")
parser.add_argument("Location", help="The location of the p4 files to be packed")
parser.add_argument("Destination", help="The destination of the ml file after packing the p4 files")
arguments =parser.parse_args()

#the location of the folder in which the p4 files are found
Folder=arguments.Location

#the destination file name for the ml code
Destination =arguments.Destination

Ocaml_code_header=" \n"

#def load_code(f_name):
chdir("./")
def load_list_of_files (destination):
  if ("." in destination):
    if (".p4" in destination):
      [destination]
      dest=destination
      while ("/" in dest):
        dest=dest[dest.find("/")+1:]
      return [dest]
    else: return []
  else:
    directories=listdir(destination)
    list_of_files=[]
    for file in directories:
      list_of_files += load_list_of_files(destination + "/"+ file)
    return list_of_files


#def add_to_map(f_name, code):
  

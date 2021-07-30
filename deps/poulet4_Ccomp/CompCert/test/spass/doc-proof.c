/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                 PROOF DOCUMENTATION                    * */
/* *                                                        * */
/* *  $Module:   DOCPROOF                                   * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2000, 2001      * */
/* *  MPI fuer Informatik                                   * */
/* *                                                        * */
/* *  This program is free software; you can redistribute   * */
/* *  it and/or modify it under the terms of the GNU        * */
/* *  General Public License as published by the Free       * */
/* *  Software Foundation; either version 2 of the License, * */
/* *  or (at your option) any later version.                * */
/* *                                                        * */
/* *  This program is distributed in the hope that it will  * */
/* *  be useful, but WITHOUT ANY WARRANTY; without even     * */
/* *  the implied warranty of MERCHANTABILITY or FITNESS    * */
/* *  FOR A PARTICULAR PURPOSE.  See the GNU General Public * */
/* *  License for more details.                             * */
/* *                                                        * */
/* *  You should have received a copy of the GNU General    * */
/* *  Public License along with this program; if not, write * */
/* *  to the Free Software Foundation, Inc., 59 Temple      * */
/* *  Place, Suite 330, Boston, MA  02111-1307  USA         * */
/* *                                                        * */
/* *                                                        * */
/* $Revision: 21527 $                                        * */
/* $State$                                            * */
/* $Date: 2005-04-24 21:10:28 -0700 (Sun, 24 Apr 2005) $                             * */
/* $Author: duraid $                                       * */
/* *                                                        * */
/* *             Contact:                                   * */
/* *             Christoph Weidenbach                       * */
/* *             MPI fuer Informatik                        * */
/* *             Stuhlsatzenhausweg 85                      * */
/* *             66123 Saarbruecken                         * */
/* *             Email: weidenb@mpi-sb.mpg.de               * */
/* *             Germany                                    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


/* $RCSfile$ */

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "doc-proof.h"

/**************************************************************/
/* Global Variables                                           */
/**************************************************************/

int dp_DEPTH;


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void dp_Init(void)
{
  dp_DEPTH = 0;
}


static void dp_FPrintDFGProof(LIST Clauses, const char *FilePrefix,
			      FLAGSTORE Flags, PRECEDENCE Precedence)
/*********************************************************
  INPUT:   A list of clauses representing a proof, a
           string indicating a file name prefix, a flag
	   store and a precedence.
  RETURNS: void.
  EFFECT:  Outputs the proof in DFG proof format to
           <FilePrefix>.prf
**********************************************************/
{
  FILE   *Output;
  CLAUSE Clause;
  LIST   AxClauses,ConClauses,ProofClauses,Scan;
  char   *name;

  AxClauses = ConClauses = ProofClauses = list_Nil();
  
  name = memory_Malloc(sizeof(char)*(strlen(FilePrefix)+5));
  sprintf(name,"%s.prf", FilePrefix);

  Output = misc_OpenFile(name,"w");

  fputs("begin_problem(Unknown).\n\n", Output);

  fputs("list_of_descriptions.\n", Output);
  fputs("name({*", Output);
  fputs(FilePrefix, Output);
  fputs("*}).\n", Output);
  fputs("author({*SPASS ", Output);
  fputs(misc_VERSION, Output);
  fputs("*}).\n", Output);
  fputs("status(unsatisfiable).\n", Output);
  fputs("description({*File generated by SPASS containing a proof.*}).\n", Output);
  fputs("end_of_list.\n\n", Output);

  fputs("list_of_symbols.\n", Output);
  fol_FPrintDFGSignature(Output);
  fputs("end_of_list.\n\n", Output);

  for (Scan=Clauses;!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    Clause = (CLAUSE)list_Car(Scan);
    if (clause_IsFromInput(Clause)) {
      if (clause_GetFlag(Clause, CONCLAUSE))
	ConClauses = list_Cons(Clause, ConClauses);
      else
	AxClauses  = list_Cons(Clause, AxClauses);
    }
    else
      ProofClauses  = list_Cons(Clause, ProofClauses);
  }

  ConClauses   = list_NReverse(ConClauses);
  AxClauses    = list_NReverse(AxClauses);
  ProofClauses = list_NReverse(ProofClauses);
  
  clause_FPrintCnfDFG(Output, FALSE, AxClauses, ConClauses, Flags, Precedence);
  fputs("\nlist_of_proof(SPASS).\n", Output);
  for (Scan=ProofClauses; !list_Empty(Scan); Scan=list_Cdr(Scan)) {
    clause_FPrintDFGStep(Output,list_Car(Scan),TRUE);
  }
  fputs("end_of_list.\n\n", Output);

  fputs("end_problem.\n\n", Output);

  misc_CloseFile(Output, name);
  fputs("\nDFG Proof printed to: ", stdout);
  puts(name);

  list_Delete(ConClauses);
  list_Delete(AxClauses);
  list_Delete(ProofClauses);
  memory_Free(name, sizeof(char)*(strlen(FilePrefix)+5));
}

LIST dp_PrintProof(PROOFSEARCH Search, LIST Clauses, const char *FilePrefix)
/*********************************************************
  INPUT:   A proofsearch object, a list of empty clauses and
           the prefix of the output file name.
  RETURNS: The list of clauses required for the proof.
  MEMORY:  The returned list must be freed.
  EFFECT:  The proof is printed both to standard output and
           to the file <FilePrefix>.prf.
**********************************************************/
{
  LIST ProofClauses,Scan,EmptyClauses,AllClauses, ReducedProof;
  LIST Missing, Incomplete, SplitClauses;

  FLAGSTORE Flags;

  Flags = prfs_Store(Search);

  Missing = pcheck_ConvertParentsInSPASSProof(Search, Clauses);
  
  if (!list_Empty(Missing)) {
    puts("\nNOTE: clauses with following numbers have not been found:");
    for (; !list_Empty(Missing); Missing = list_Pop(Missing))
      printf("%d ", (int)list_Car(Missing)); 
    putchar('\n');
  }

  EmptyClauses = list_Copy(Clauses); 
  ProofClauses = list_Nil();
  AllClauses   = list_Nconc(list_Copy(prfs_DocProofClauses(Search)),
			    list_Nconc(list_Copy(prfs_UsableClauses(Search)),
				       list_Copy(prfs_WorkedOffClauses(Search))));

  /*
   *  collect proof clauses by noodling upward in the 
   *  proof tree, starting from <EmptyClauses>.
   *  Before, add all splitting clauses to avoid gaps in split tree 
   */

  SplitClauses = list_Nil();
  for (Scan = AllClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) 
    if (clause_IsFromSplitting(list_Car(Scan))) 
      SplitClauses = list_Cons(list_Car(Scan), SplitClauses);

  /* mark all needed clauses */
  pcheck_ClauseListRemoveFlag(EmptyClauses, MARKED);
  pcheck_ClauseListRemoveFlag(AllClauses, MARKED);
  pcheck_MarkRecursive(EmptyClauses);
  pcheck_MarkRecursive(SplitClauses);
  
  /* collect all marked clauses */
  ProofClauses = list_Nil();
  for (Scan = AllClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    if (clause_GetFlag(list_Car(Scan), MARKED))
      ProofClauses = list_Cons(list_Car(Scan), ProofClauses); 
  }

  /* build reduced proof  */
  ProofClauses = list_Nconc(ProofClauses, list_Copy(EmptyClauses));
  ProofClauses = pcheck_ClauseNumberMergeSort(ProofClauses);
  ReducedProof = pcheck_ReduceSPASSProof(ProofClauses); 

  dp_SetProofDepth(pcheck_SeqProofDepth(ReducedProof));
  
  pcheck_ParentPointersToParentNumbers(AllClauses);
  pcheck_ParentPointersToParentNumbers(Clauses);

  /* check reduced proof for clauses whose parents have been marked as
     incomplete (HIDDEN flag) by ConvertParentsInSPASSProof    */

  Incomplete = list_Nil();
  for (Scan = ReducedProof; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    if (clause_GetFlag(list_Car(Scan), HIDDEN))
      Incomplete = list_Cons(list_Car(Scan), Incomplete);
  }
  if (!list_Empty(Incomplete)) {
    puts("NOTE: Following clauses in reduced proof have incomplete parent sets:");
    for (Scan = Incomplete; !list_Empty(Scan); Scan = list_Cdr(Scan))
      printf("%d ", clause_Number(list_Car(Scan)));
    putchar('\n');
  }

  printf("\n\nHere is a proof with depth %d, length %d :\n",
	 dp_ProofDepth(), list_Length(ReducedProof));
  clause_ListPrint(ReducedProof);

  if (flag_GetFlagValue(Flags, flag_FPDFGPROOF))
    dp_FPrintDFGProof(ReducedProof, FilePrefix, Flags, prfs_Precedence(Search));

  fflush(stdout);

  list_Delete(EmptyClauses);
  list_Delete(AllClauses);
  list_Delete(ProofClauses);
  list_Delete(SplitClauses);
  list_Delete(Incomplete); 

  return ReducedProof;
}





/******************************************************************************/
/*									      */
/*	All the stuff for trying possible next literals, growing clauses      */
/*	and assembling definitions					      */
/*									      */
/******************************************************************************/

#include  "defns.i"
#include  "extern.i"

int FalsePositive, FalseNegative;

void FindDefinition(Relation R)
/*    --------------  */ {
    printf("DEBUG: FindDefinition(): Entering!\n");
    int Size, i, TargetPos, FirstDefR;

    Target = R;
    NCl = 0;

    printf("\n----------\n%s:\n", R->Name);

    /*  Reorder the relations so that the target relation comes first  */

    printf("DEBUG: Reordering the relations so that the target relation comes first!\n");
    FirstDefR = (RelnOrder[2] == GTVAR ? 4 : 2);

    for (TargetPos = FirstDefR; RelnOrder[TargetPos] != Target;
            TargetPos++);

    for (i = TargetPos; i > FirstDefR; i--) {
        RelnOrder[i] = RelnOrder[i - 1];
    }
    RelnOrder[FirstDefR] = Target;
    printf("DEBUG: Done reordering the relations!\n");

    /*  Generate initial tuples and make a copy  */

    printf("DEBUG: Generate initial tuples and make a copy!\n");
    OriginalState(R);

    printf("DEBUG: FindDefinition(): CREATE LABELS VECTOR HERE!\n");
    printf("DEBUG: Number of examples = %d\n", StartDef.NTot);

    lp.num_examples = StartDef.NTot;
    lp.labels = new int[lp.num_examples];
    Tuple* tmp = StartDef.Tuples;
    for (int i = 0; i < lp.num_examples; ++i) {
        lp.labels[i] = Positive(*tmp++) != 0;
        printf("DEBUG: [%d] label set as %d\n", i, lp.labels[i]);
    }

    StartClause = StartDef;

    Size = StartDef.NTot + 1;
    StartClause.Tuples = Alloc(Size, Tuple);
    memcpy(StartClause.Tuples, StartDef.Tuples, Size * sizeof (Tuple));

    NRecLitDef = 0;

    FalsePositive = 0;
    FalseNegative = StartDef.NPos;

    R->Def = Alloc(100, Clause);
    printf("DEBUG: Done generate initial tuples and make a copy!\n");

    while (StartClause.NPos) {
        printf("DEBUG: StartClause.NPos = %d!\n", StartClause.NPos);
        if (!(R->Def[NCl] = FindClause()))
            break;

        R->Def[NCl++][NLit] = Nil;

        if (NCl % 100 == 0) {
            Realloc(R->Def, NCl + 100, Clause);
        }

        NRecLitDef += NRecLitClause;
    }
    printf("DEBUG: Loop exit! StartClause.NPos = %d!\n", StartClause.NPos);
    R->Def[NCl] = Nil;

    printf("DEBUG: Sifting the clauses!\n");
    SiftClauses();
    printf("DEBUG: Done sifting the clauses!\n");

    if (FalsePositive || FalseNegative) {
        printf("\n***  Warning: the following definition\n");

        if (FalsePositive) {
            printf("***  matches %d tuple%s not in the relation\n",
                    FalsePositive, Plural(FalsePositive));
        }

        if (FalseNegative) {
            printf
                    ("***  does not cover %d tuple%s in the relation\n",
                    FalseNegative, Plural(FalseNegative));
        }
    }

    printf("DEBUG: Printing the definitions!\n");
    PrintDefinition(R);
    printf("DEBUG: Done printing the definitions!\n");

    pfree(StartClause.Tuples);
    pfree(StartDef.Tuples);

    /*  Restore original relation order  */

    for (i = FirstDefR; i < TargetPos; i++) {
        RelnOrder[i] = RelnOrder[i + 1];
    }
    RelnOrder[TargetPos] = Target;

    printf("DEBUG: FindDefinition(): Leaving!\n");
}

Clause FindClause()
/*      ----------  */ {
    printf("DEBUG: FindClause(): Entering!\n");
    Tuple Case, *TSP;

    printf("DEBUG: Initializing clause info!\n");
    InitialiseClauseInfo();
    printf("DEBUG: Done Initializing clause info!\n");

    printf("DEBUG: Growing new clause!\n");
    GrowNewClause();
    printf("DEBUG: Done Growing new clause!\n");

    /*  Now that pruning includes addition of implicit equalities,
       should try even when there is a single RHS literal  */

    printf("DEBUG: Pruning new clause!\n");
    PruneNewClause();
    printf("DEBUG: Done Pruning new clause!\n");

    /*  Make sure accuracy criterion is satisfied  */

    if (!NLit
            || Current.NOrigPos + 1E-3 < AdjMinAccuracy * Current.NOrigTot) {
        if (NLit) {
            Verbose(1)
            printf("\nClause too inaccurate (%d/%d)\n",
                    Current.NOrigPos, Current.NOrigTot);
        }

        pfree(NewClause);
        return Nil;
    }

    FalsePositive += Current.NOrigTot - Current.NOrigPos;
    FalseNegative -= Current.NOrigPos;

    /*  Set flags for positive covered tuples  */

    ClearFlags;

    for (TSP = Current.Tuples; Case = *TSP; TSP++) {
        if (Positive(Case)) {
            SetFlag(Case[0] & Mask, TrueBit);
        }
    }

    if (Current.Tuples != StartClause.Tuples) {
        FreeTuples(Current.Tuples, true);
    }

    /*  Copy all negative tuples and uncovered positive tuples  */

    StartClause.NTot = StartClause.NPos = 0;

    for (TSP = StartClause.Tuples; Case = *TSP; TSP++) {
        if (!Positive(Case) || !TestFlag(Case[0] & Mask, TrueBit)) {
            StartClause.Tuples[StartClause.NTot++] = Case;
            if (Positive(Case))
                StartClause.NPos++;
        }
    }
    StartClause.Tuples[StartClause.NTot] = Nil;

    StartClause.NOrigPos = StartClause.NPos;
    StartClause.NOrigTot = StartClause.NTot;

    StartClause.BaseInfo = Info(StartClause.NPos, StartClause.NTot);
    Current = StartClause;

    Verbose(1) {
        printf("\nClause %d: ", NCl);
        PrintClause(Target, NewClause);
    }

    printf("DEBUG: FindClause(): Leaving!\n");
    return NewClause;
}

void ExamineLiterals()
/*    ---------------  */ {
    printf("DEBUG: ExamineLiterals(): Entering!\n");
    Relation R;
    int i, Relns = 0;

    NPossible = NDeterminate = 0;

    MaxPossibleGain = Current.NPos * Current.BaseInfo;

    /*  If this is not the first literal, review coverage and check
       variable orderings, identical variables etc.  */

    if (NLit != 0) {
        CheckOriginalCaseCover();
        ExamineVariableRelationships();
    }

    AvailableBits = Encode(Current.NOrigPos) - ClauseBits;

    Verbose(1) {
        printf("\nState (%d/%d", Current.NPos, Current.NTot);
        if (Current.NTot != Current.NOrigTot) {
            printf(" [%d/%d]", Current.NOrigPos, Current.NOrigTot);
        }
        printf(", %.1f bits available", AvailableBits);

        if (NWeakLits) {
            Verbose(2)
            printf(", %d weak literal%s", NWeakLits,
                    Plural(NWeakLits));
        }
        printf(")\n");

        Verbose(4)
        PrintTuples(Current.Tuples, Current.MaxVar);
    }

    /*  Find possible literals for each relation  */

    printf("DEBUG: Find possible literals for each relation!\n");

    ForEach(i, 0, MaxRel) {
        R = RelnOrder[i];

        printf("DEBUG: [%d] Exploring args for %s\n", i, R->Name);
        ExploreArgs(R, true);

        if (R->NTrialArgs)
            Relns++;
    }
    printf("DEBUG: Done Finding possible literals for each relation!\n");

    /*  Evaluate them  */

    AlterSavedClause = Nil;
    Verbose(2) putchar('\n');

    for (i = 0; i <= MaxRel && BestLitGain < MaxPossibleGain; i++) {
        R = RelnOrder[i];
        printf("DEBUG: [%d] Evaluating for %s\n", i, R->Name);
        printf("DEBUG: %s.NTrialArgs = %d\n", R->Name, R->NTrialArgs);
        if (!R->NTrialArgs) {
            printf("DEBUG: skipping!\n");
            continue;
        }

        R->Bits = Log2(Relns) + Log2(R->NTrialArgs + 1E-3);
        if (NEGLITERALS || Predefined(R))
            R->Bits += 1.0;

        if (R->Bits - Log2(NLit + 1.001 - NDetLits) > AvailableBits) {

            Verbose(2) {
                printf("\t\t\t\t[%s requires %.1f bits]\n",
                        R->Name, R->Bits);
            }
        } else {
            ExploreArgs(R, false);

            Verbose(2)
            printf("\t\t\t\t[%s tried %d/%d] %.1f secs\n",
                    R->Name, R->NTried, R->NTrialArgs,
                    CPUTime());
        }
    }
    printf("DEBUG: ExamineLiterals(): Leaving!\n");
}

void GrowNewClause()
/*    -------------                */ {
    printf("DEBUG: GrowNewClause(): Entering!\n");
    Literal L;
    int i, OldNLit;
    Boolean Progress = true;
    float Accuracy, ExtraBits;

    int iteration = 0;

    printf("DEBUG: Checking literals in loop!\n");
    while (Progress && Current.NPos < Current.NTot) {
        printf("DEBUG: iteration : %d\n", iteration++);

        printf("DEBUG: ---- Examining the literals!\n");
        ExamineLiterals();
        printf("DEBUG: ---- Done Examining the literals!\n");

        /*  If have noted better saveable clause, record it  */

        if (AlterSavedClause) {
            printf("DEBUG: Altering saved clause!\n");
            Realloc(SavedClause, NLit + 2, Literal);

            ForEach(i, 0, NLit - 1) {
                SavedClause[i] = NewClause[i];
            }
            SavedClause[NLit] = AllocZero(1, struct _lit_rec);
            SavedClause[NLit + 1] = Nil;

            SavedClause[NLit]->Rel = AlterSavedClause->Rel;
            SavedClause[NLit]->Sign = AlterSavedClause->Sign;
            SavedClause[NLit]->Args = AlterSavedClause->Args;
            SavedClause[NLit]->Bits = AlterSavedClause->Bits;
            SavedClause[NLit]->WeakLits = 0;

            SavedClauseCover = AlterSavedClause->PosCov;
            SavedClauseAccuracy = AlterSavedClause->PosCov /
                    (float) AlterSavedClause->TotCov;

            Verbose(1) {
                printf("\n\tSave clause ending with ");
                PrintLiteral(SavedClause[NLit]);
                printf(" (cover %d, accuracy %d%%)\n",
                        SavedClauseCover,
                        (int) (100 * SavedClauseAccuracy));
            }

            pfree(AlterSavedClause);
            printf("DEBUG: Done Altering saved clause!\n");
        }

        if (NDeterminate && BestLitGain < DETERMINATE * MaxPossibleGain) {
            ProcessDeterminateLiterals(true);
        } else if (NPossible) {
            /*  At least one gainful literal  */

            NewClause[NLit] = L = SelectLiteral();
            if (++NLit % 100 == 0)
                Realloc(NewClause, NLit + 100, Literal);

            ExtraBits = L->Bits - Log2(NLit - NDetLits + 1E-3);
            ClauseBits += Max(ExtraBits, 0);

            Verbose(1) {
                printf("\nBest literal ");
                PrintLiteral(L);
                printf(" (%.1f bits)\n", L->Bits);
            }

            /*  Check whether should regrow clause  */

            if (L->Rel != Target && AllLHSVars(L) &&
                    Current.MaxVar > Target->Arity && !AllDeterminate()) {
                OldNLit = NLit;
                NLit = 0;

                ForEach(i, 0, OldNLit - 1) {
                    if (AllLHSVars(NewClause[i])) {
                        NewClause[NLit++] =
                                NewClause[i];
                    }
                }
                NewClause[NLit] = Nil;

                RecoverState(NewClause);

                Verbose(1) {
                    printf("\n[Regrow clause] ");
                    PrintClause(Target, NewClause);
                }
                GrowNewClause();
                return;
            }

            NWeakLits = L->WeakLits;

            if (L->Rel == Target)
                AddOrders(L);

            NewState(L, Current.NTot);

            if (L->Rel == Target)
                NoteRecursiveLit(L);
        } else {
            Verbose(1) printf("\nNo literals\n");

            Progress = Recover();
        }
    }
    printf("DEBUG: Done Checking literals in loop!\n");

    /* check if the LP formula makes sense */
    int num_rows = lp.num_examples;
    int num_cols = lp.problem.size();
    printf("Creating a matrix of size %dx%d\n", num_rows, num_cols);
    Eigen::MatrixXi A(num_rows, num_cols);
    for (int i = 0; i < num_rows; ++i) {
        for (int j = 0; j < num_cols; ++j) {
            //printf("DEBUG: example %d : ", i);
            //PrintComposedLiteral(lp.problem[j].R, true, lp.problem[j].A);
            //printf(" : entry : %d\n", lp.problem[j].entries[i]);
            A(i, j) = lp.problem[j].entries[i];
        }
    }
    Eigen::Map<Eigen::VectorXi> b(lp.labels, lp.num_examples);
    std::cout << "A = " << std::endl << A << std::endl;
    std::cout << "b = " << std::endl << b << std::endl;

    // solve the LP problem
    int num_pos_examples = 0;
    for (int i = 0; i < b.rows(); ++i) {
        if (b[i])
            num_pos_examples++;
    }
    int num_literals = num_cols;
    int num_examples = lp.num_examples;
    std::cout << "num_pos_examples = " << num_pos_examples << std::endl;
    std::cout << "num_literals = " << num_literals << std::endl;

    glp_prob *glp;
    double z, x;

    glp = glp_create_prob();
    glp_set_prob_name(glp, "1Rule");
    glp_set_obj_dir(glp, GLP_MIN);

    num_rows = num_examples;
    num_cols = num_literals + num_examples; // adding num_examples for the regularizer
    int size = num_rows * num_cols;

    // regularization parameter
    double lambda = 0.5;

    int *ia = new int[size + 1]();
    int *ja = new int[size + 1]();
    double *ar = new double[size + 1]();

    glp_add_rows(glp, num_rows);
    glp_add_cols(glp, num_cols);

    for (int i = 0; i < num_cols; ++i) {
        //glp_set_col_name(lp, i+1, (string("x") + to_string(i)).c_str());

        // adding weight variables w_i, doubly bounded 0 <= w_i <= 1
        if (i < num_literals) {
            glp_set_col_bnds(glp, i + 1, GLP_DB, 0.0, 1.0);
            glp_set_obj_coef(glp, i + 1, 1);
        } else // adding slack variables
        {
            // bounds on slack variables are different for positive and negative examples
            if (i < num_literals + num_pos_examples) {
                // for positive examples, doubly bound l_i, 0 <= l_i <= 1
                glp_set_col_bnds(glp, i + 1, GLP_DB, 0.0, 1.0);
                glp_set_obj_coef(glp, i + 1, lambda);
            } else {
                // for negative examples, lower bounded l_i, 0 <= l_i
                glp_set_col_bnds(glp, i + 1, GLP_LO, 0.0, 0.0);
                glp_set_obj_coef(glp, i + 1, lambda);
            }
        }
    }

    // adding the matrix - Aw
    int idx = 1;
    for (int i = 0; i < num_rows; ++i) {
        for (int j = 0; j < num_cols; ++j) {
            //cout << "idx = " << idx << endl;
            ia[idx] = i + 1;
            ja[idx] = j + 1;
            if (j < num_literals)
                ar[idx] = A(i, j); /* a[1,1] = 1 */
            else
                ar[idx] = 0;
            //cout << "A[" << ia[idx] << "," << ja[idx] << "]=" << ar[idx] << endl;
            idx++;
        }
    }

    // adding condition on matrix entries - this differs for positive and negative
    // examples. for positive, its lower bounded, 1 <= Aw
    // for negative its equality bounded, Aw = 0
    for (int i = 0; i < num_rows; ++i) {
        //string name = string("p_") + to_string(i);
        //glp_set_row_name(lp, i+1, name.c_str());
        //double d = CMath::random(0.0, 10.0);
        //cout << "-infty < " << name << " < " << d << endl;
        if (i < num_pos_examples)
            glp_set_row_bnds(glp, i + 1, GLP_LO, 1.0, 0.0);
        else
            glp_set_row_bnds(glp, i + 1, GLP_FX, 0.0, 0.0);
    }

    glp_load_matrix(glp, num_rows*num_cols, ia, ja, ar);
    glp_simplex(glp, NULL);
    z = glp_get_obj_val(glp);

    printf("\nz = %g;", z);
    for (int i = 0; i < num_literals; ++i) {
        x = glp_get_col_prim(glp, i + 1);
        printf("w%d = %g ", x, i + 1);
    }
    printf("\n");
    // printing the solution
    printf("DEBUG: Selected clauses by LP!\n");
    for (int i = 0; i < num_literals; ++i)
    {
        x = glp_get_col_prim(glp, i + 1);
        if (x > 0)
        {
            // this means that this clause has been selected
            PrintComposedLiteral(lp.problem[i].R, true, lp.problem[i].A);
        }
    }
    
    glp_delete_prob(glp);

    // foil stuff
    NewClause[NLit] = Nil;

    /*  Finally, see whether saved clause is better  */

    CheckOriginalCaseCover();
    Accuracy = Current.NOrigPos / (float) Current.NOrigTot;
    if (SavedClause &&
            (SavedClauseAccuracy > Accuracy ||
            SavedClauseAccuracy == Accuracy &&
            SavedClauseCover > Current.NOrigPos ||
            SavedClauseAccuracy == Accuracy &&
            SavedClauseCover == Current.NOrigPos &&
            CodingCost(SavedClause) < CodingCost(NewClause))) {
        Verbose(1) printf("\n[Replace by saved clause]\n");
        RecoverState(SavedClause);
        CheckOriginalCaseCover();
    }
    printf("DEBUG: GrowNewClause(): Leaving!\n");
}

void InitialiseClauseInfo()
/*  --------------------  */ {
    Var V;

    /*  Initialise everything for start of new clause  */

    NewClause = Alloc(100, Literal);

    Current = StartClause;

    NLit = NDetLits = NWeakLits = NRecLitClause = 0;

    NToBeTried = 0;
    AnyPartialOrder = false;

    ClauseBits = 0;

    ForEach(V, 1, Target->Arity) {
        Variable[V]->Depth = 0;
        Variable[V]->Type = Target->Type[V];
        Variable[V]->TypeRef = Target->TypeRef[V];
    }

    memset(Barred, false, MAXVARS + 1);

    SavedClause = Nil;
    SavedClauseAccuracy = SavedClauseCover = 0;

    MAXRECOVERS = MAXALTS;
}

Boolean SameLiteral(Relation R, Boolean Sign, Var * A)
/*       -----------  */ {
    Var V, NArgs;

    if (R != AlterSavedClause->Rel || Sign != AlterSavedClause->Sign) {
        return false;
    }

    NArgs = (HasConst(R) ? 1 + sizeof (Const) : R->Arity);

    ForEach(V, 1, NArgs) {
        if (A[V] != AlterSavedClause->Args[V])
            return false;
    }

    return true;
}

Boolean AllLHSVars(Literal L)
/*       ----------  */ {
    Var V;

    ForEach(V, 1, L->Rel->Arity) {
        if (L->Args[V] > Target->Arity)
            return false;
    }

    return true;
}

/*  See whether all literals in clause are determinate  */

Boolean AllDeterminate()
/*       --------------  */ {
    int i;

    ForEach(i, 0, NLit - 2) {
        if (NewClause[i]->Sign != 2)
            return false;
    }

    return true;
}

/*  Find the coding cost for a clause  */

float CodingCost(Clause C)
/*      ----------  */ {
    float SumBits = 0, Contrib;
    int Lits = 0;

    while (*C) {
        Lits++;
        if ((Contrib = (*C)->Bits - Log2(Lits)) > 0)
            SumBits += Contrib;
        C++;
    }

    return SumBits;
}

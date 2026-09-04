#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* Antihydra 1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA
   states A..F = 0..5. halt at (F,0)=(5,0). */
static const int wr[6][2]   = {{1,1},{0,1},{1,1},{1,0},{1,1},{0,0}};
static const int mv[6][2]   = {{+1,+1},{-1,-1},{-1,-1},{-1,-1},{-1,+1},{0,+1}}; /*R=+1,L=-1*/
static const int nx[6][2]   = {{1,0},{2,4},{3,2},{0,1},{5,4},{5,0}};
/* halt = state5 reading 0 */
int main(void){
    long OFF=32;
    long CAP=2L*10000+64+OFF;   /* index space */
    unsigned char *tape=calloc(CAP+8,1);
    long mismatches=0; long lastc=0; long long lastt=0;
    long long grand=0;
    for(long c=1;c<=10000;c+=2){
        long span=2*c+64;              /* clear indices [0, span+OFF] */
        memset(tape,0,span+OFF+1);
        /* materialize (1,2,c) at p=0: a=1 at pos0; m=2 at pos2,3; c-block pos5..4+c; head=c+5 */
        long p=0;
        tape[p+0+OFF]=1;               /* a block, a=1 */
        tape[p+2+OFF]=1; tape[p+3+OFF]=1; /* m=2 */
        for(long i=0;i<c;i++) tape[p+5+i+OFF]=1; /* c block */
        long head=c+5; int st=1; /* state B=1 */
        long long steps=0;
        for(;;){
            long idx=head+OFF;
            int b=tape[idx];
            if(st==5 && b==0){ break; } /* halt */
            tape[idx]=(unsigned char)wr[st][b];
            head+=mv[st][b];
            st=nx[st][b];
            steps++;
            /* safety: head must stay in bounds */
            if(head+OFF<0 || head+OFF>span+OFF){ fprintf(stderr,"OOB c=%ld head=%ld\n",c,head); return 2;}
        }
        long long formula=(3LL*c*c+44LL*c+125)/4;
        if(steps!=formula){ mismatches++; if(mismatches<=20) printf("MISS c=%ld steps=%lld formula=%lld\n",c,steps,formula);}
        lastc=c; lastt=steps; grand+=steps;
    }
    printf("odd c=1..%ld (step 2) verified by direct raw simulation\n",lastc);
    printf("mismatches vs (3c^2+44c+125)/4: %ld\n",mismatches);
    printf("largest: c=%ld halted at %lld raw steps (formula %lld)\n",lastc,lastt,(3LL*lastc*lastc+44LL*lastc+125)/4);
    printf("total raw steps simulated: %lld\n",grand);
    free(tape);
    return mismatches? 1:0;
}

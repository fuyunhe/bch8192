/*******************************************************************************
*
*    File Name:  bch_decoder.c
*     Revision:  1.0
*         Date:  August, 2006
*
* Rev  Author			Date		Changes
* ---  ---------------	----------	-------------------------------
* 1.0  ZS				08/07/2006	Initial release
* 
* 
/*******************************************************************************/

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define mm_max  13         	/* Dimension of Galoise Field */
#define nn_max  8192        	/* Length of codeword, n = 2**m - 1 */
#define tt_max  10          	/* Number of errors that can be corrected */
#define kk_max  8192        	/* Length of information bit, kk = nn - rr  */
#define rr_max  130			/* Number of parity checks, rr = deg[g(x)] */

#define		k_tt		8
#define		k_ttx2		(k_tt*2)

int pp_mask;
int mm, nn, kk, tt, rr, length;		// BCH code parameters
int p[mm_max + 1], alpha_to[nn_max], index_of[nn_max] ;	// Galois field
int gg[rr_max] ;		// Generator polynomial
int data[kk_max], recd[nn_max] ;	// Information data and received data


int bb[rr_max] ;	// Syndrome polynomial
int s[rr_max];		// Syndrome values
int syn_error;		// Syndrome error indicator
int count;		// Number of errors
int location[tt_max];	// Error location

int decode_flag;	// Decoding indicator 
void encode_bch(int *pdata);

int GFMult(int X1, int X2)
{
	int i, result = 0;
	for(i = mm-1; i >= 0; i--){
		result <<= 1;
		if(X2 & (1 << i))
			result ^= X1;
		
		if(result & (1 << mm))
			result ^= (1 << mm) | pp_mask;
	}
	
	return result;
}

void generate_gf()
/* Generate GF(2**mm) from the primitive polynomial p(X) in p[0]..p[mm]
The lookup table looks like:  
index -> polynomial form:   alpha_to[ ] contains j = alpha**i;
polynomial form -> index form:  index_of[j = alpha**i] = i
alpha_to[1] = 2 is the primitive element of GF(2**mm)
*/
{
	int i;
	int mask ;	// Register states
	
	// Primitive polynomials
   	for (i = 1; i < mm; i++)
		p[i] = 0;
	p[0] = p[mm] = 1;
	if (mm == 2)		p[1] = 1;
	else if (mm == 3)	p[1] = 1;
	else if (mm == 4)	p[1] = 1;
	else if (mm == 5)	p[2] = 1;
	else if (mm == 6)	p[1] = 1;
	else if (mm == 7)	p[1] = 1;
	else if (mm == 8)	p[4] = p[5] = p[6] = 1;
	else if (mm == 9)	p[4] = 1;
	else if (mm == 10)	p[3] = 1;
	else if (mm == 11)	p[2] = 1;
	else if (mm == 12)	p[3] = p[4] = p[7] = 1;
	else if (mm == 13)	p[1] = p[2] = p[3] = p[5] = p[7] = p[8] = p[10] = 1;	// 25AF
	//	else if (mm == 13)	p[1] = p[3] = p[4] = 1;
	else if (mm == 14)	p[2] = p[4] = p[6] = p[7] = p[8] = 1;	// 41D5
	// else if (mm == 14)	p[1] = p[11] = p[12] = 1;
	else if (mm == 15)	p[1] = 1;
	else if (mm == 16)	p[2] = p[3] = p[5] = 1;
	else if (mm == 17)	p[3] = 1;
	else if (mm == 18)	p[7] = 1;
	else if (mm == 19)	p[1] = p[5] = p[6] = 1;
	else if (mm == 20)	p[3] = 1;
	
	
	fprintf(stderr, "# The Galois field is GF(2**%d);\n\n", mm);
	fprintf(stderr, "# The primitive polynomial is: p(x) = ");
	for (i = 0; i <= mm; i++) 
	{
		fprintf(stderr, " %d", p[i]);
	}
	fprintf(stderr, "\n\n");
	
	// Galois field implementation with shift registers
	// Ref: L&C, Chapter 6.7, pp. 217
	mask = 1 ;
	alpha_to[mm] = 0 ;
	for (i = 0; i < mm; i++)
	{ 
		alpha_to[i] = mask ;
		index_of[alpha_to[i]] = i ;
		if (p[i] != 0)
			alpha_to[mm] ^= mask ;
		
		mask <<= 1 ;
	}
	
	pp_mask = alpha_to[mm];
	
	index_of[alpha_to[mm]] = mm ;
	mask >>= 1 ;
	for (i = mm + 1; i < nn; i++)
	{ 	
		if (alpha_to[i-1] >= mask)
			alpha_to[i] = alpha_to[mm] ^ ((alpha_to[i-1] ^ mask) << 1) ;
		else alpha_to[i] = alpha_to[i-1] << 1 ;
		
		index_of[alpha_to[i]] = i ;
	}
	index_of[0] = -1 ;
	
	
	// Print out the Galois Field	
	
	//	fprintf(stderr, "# Look-up tables for GF(2**%2d)\n", mm) ;
	//	fprintf(stderr, "  i   alpha_to[i]  index_of[i]\n") ;
	//	for (i=0; i<=nn; i++)
	//		fprintf(stderr, "%3d      %3d          %3d\n", i, alpha_to[i], index_of[i]) ;
	//	fprintf(stderr, "\n") ;
	
	//	fprintf(stdout, "# Look-up tables for GF(2**%2d)\n", mm) ;
	//	fprintf(stdout, "  i   alpha_to[i]  index_of[i]\n") ;
	//	for (i=0; i<=nn; i++)
	//		fprintf(stdout, "%3d      %3d          %3d\n", i, alpha_to[i], index_of[i]) ;
	//	fprintf(stdout, "\n") ;
	
}


void gen_poly()
/* Compute generator polynomial of the tt-error correcting Binary BCH code 
* g(x) = LCM{M_1(x), M_2(x), ..., M_2t(x)},
* where M_i(x) is the minimal polynomial of alpha^i by cyclotomic cosets
*/
{
	//int gen_roots[nn + 1], gen_roots_true[nn + 1] ; 	// Roots of generator polynomial
	int *gen_roots = (int*)malloc(sizeof(int)*(nn + 1));
	int *gen_roots_true = (int*)malloc(sizeof(int)*(nn + 1));
	
	int i, j, Temp ;
	
	// Initialization of gen_roots
	for (i = 0; i <= nn; i++) 
	{	
		gen_roots_true[i] = 0;
		gen_roots[i] = 0;
	}
	
	// Cyclotomic cosets of gen_roots
   	for (i = 1; i <= 2*tt ; i++)
	{
		for (j = 0; j < mm; j++) 
		{
			Temp = ((int)pow(2, j) * i) % nn;
			gen_roots_true[Temp] = 1;
		}
	}
	
   	rr = 0;		// Count the number of parity check bits
   	for (i = 0; i < nn; i++) 
	{
		if (gen_roots_true[i] == 1) 
		{	
			rr++;
			gen_roots[rr] = i;
		}
	}
	//	kk = nn - rr;
	
	// Compute generator polynomial based on its roots
	gg[0] = 2 ;	// g(x) = (X + alpha) initially
	gg[1] = 1 ;
	for (i = 2; i <= rr; i++)
	{ 	
		gg[i] = 1 ;
		for (j = i - 1; j > 0; j--)
			if (gg[j] != 0)  
				gg[j] = gg[j-1]^ alpha_to[(index_of[gg[j]] + index_of[alpha_to[gen_roots[i]]]) % nn] ;
			else 
				gg[j] = gg[j-1] ;
			gg[0] = alpha_to[(index_of[gg[0]] + index_of[alpha_to[gen_roots[i]]]) % nn] ;
	}
	
	
	fprintf(stderr, "# The Generator Polynomial is:\n") ;
	for (i=0; i <= rr; i++)  
		fprintf(stderr, " %d", gg[i]) ;
	fprintf(stderr, "\n\n") ;
}

void decode_bch()
{
	register int i, j, elp_sum ;
	int r;				// Iteration steps
	int Delta; 			// Discrepancy value
	int elp[k_ttx2+1][k_ttx2+2]; 	// Error locator polynomial (ELP)
	int L[k_ttx2+1];			// Degree of ELP 
	int B[k_ttx2+1][k_ttx2+2];		// Scratch polynomial
	int root[k_tt+1];			// Roots of ELP 
	int reg[k_tt+1];			// Register state
	int	deltacoef = 0;
	int	DeltaB, p;
	int	bb_val;
	int dummy_elp[k_tt+1];		// this is constant value...
	
	encode_bch(recd);			//Decoded, using the same as the encode...
	for (i = 0; i < (length - kk)/8; i++)
		bb[i] ^= recd[i+kk/8];

	//make bb to bits.....

	for (i = 1; i <= k_ttx2; i++)				// Reset 
		s[i] = 0;
	
	for (j = 0; j < length - kk; j++)			// Each redundant data input then calc..
	{
		bb_val = bb[j/8] & (1 << (7-(j&0x7)));
		for (i = 1; i <= k_ttx2; i++) 
		{
			//if (bb[j] != 0)
			if(bb_val != 0)
				s[i] ^= alpha_to[(i * j) % nn];
		}
	}
	
	for (i = 1; i <= k_ttx2; i++)					// ERROR DETECTION
	{
		if (s[i] != 0)
			syn_error = 1; // set error flag if non-zero syndrome 
	}
/*
	for (i = 1; i <= t2; i++) {
		s[i] = 0;
		for (j = 0; j < length - kk; j++)
			if (bb[j] != 0)
				s[i] ^= alpha_to[(i * j) % nn];
			if (s[i] != 0)
				syn_error = 1; // set error flag if non-zero syndrome 
			
			// Note:    If the code is used only for ERROR DETECTION, then
			//         exit program here indicating the presence of errors.
			//
			// convert syndrome from polynomial form to index form  
			//		s[i] = index_of[s[i]];
			//		printf("%3d ", s[i]);
	}
*/
	
	if (!syn_error)
	{
		
		decode_flag = 1 ;	// No errors
		count = 0 ;
	}
	else	// Having errors, begin decoding procedure
	{	// Simplified Berlekamp-Massey Algorithm for Binary BCH codes
		// All values are in polynomial form
		// Ref: Blahut, pp.191, Chapter 7.6 
		// Ref: L&C, pp.212, Chapter 6.4
		
		DeltaB = 1, p=1;
		
		// Initialization of elp, B and register
		for (i = 0; i <= k_ttx2; i++)
		{
			L[i] = 0 ;
			for (j = 0; j <= k_ttx2; j++)
			{
				elp[i][j] = 0 ;
				B[i][j] = 0 ;
			}
		}
		for (i = 0; i <= tt; i++)
		{	
			root[i] = 0 ;
			reg[i] = 0 ;
		}
		elp[0][0] = 1 ;
		B[0][0] = 1;
		
		for(r = 1; r < k_ttx2; r++){
			// Compute discrepancy
			Delta = 0;
			for (i = 0; i <= L[r-1]; i++)
			{
				if ((s[r-i] != 0) && (elp[r-1][i] != 0))
					Delta ^= GFMult(s[r-i], elp[r-1][i]);
			}
			
			if(Delta == 0){
				L[r] = L[r-1] ;
				for (i = 0; i <= L[r-1]; i++)
				{
					elp[r][i] = elp[r-1][i] ;
					B[r][i] = B[r-1][i] ;
				}
				p++;
			}
			else
			{
				// Form new error locator polynomial
				for (i = 0; i <= L[r-1]; i++)
				{
					if(elp[r-1][i] != 0)
						elp[r][i] = GFMult(DeltaB, elp[r-1][i]);
				}
				for (i = 0; i <= L[r-1]; i++)
				{
					if (B[r-p][i] != 0)
						elp[r][i+p] ^= GFMult(Delta, B[r-1][i]);
				}
				
				// Form new scratch polynomial and register length
				if (2 * L[r-1] > r)
				{		
					L[r] = L[r-1] ;
					for (i = 0; i <= L[r-1]; i++)
					{
						B[r][i] = B[r-1][i];
					}
					
					p++;
				}
				else
				{
					for (i = 0; i <= L[r-1]; i++)
					{
						B[r][i] = elp[r-1][i];
					}
					
					DeltaB = Delta;
					p = 1;
					L[r] = r - L[r-1] ;
				} // else of (2 * L[r-1] >= r)
			}	// else of (Delta == 0)
		} //for(r = 0; r < k_ttx2; r++) 
		  /*
		  deltacoef = elp[15][0];
		  for(i=0; i<16; i++)
		  {
		  if (elp[15][i] != 0)
		  elp[15][i] = alpha_to[(index_of[elp[15][i]] + nn - index_of[deltacoef]) % nn ];
		  }
		*/
		
		if (L[k_ttx2-1] > tt)
		{
			decode_flag = 0;
		}
		else
		{	// Chien's search to find roots of the error location polynomial
			// Ref: L&C pp.216, Fig.6.1
			for (i = 0; i <= L[k_ttx2-1]; i++)
				reg[i] = elp[k_ttx2-1][i] ;
			count = 0 ;

#if		0
		for (i = 1; i <= nn; i++)
#else
			for (j = 1; j <= L[k_ttx2-1]; j++)
				dummy_elp[j] = 1;
			for (i = 1; i <= nn-length; i++){
				for (j = 1; j <= L[k_ttx2-1]; j++)
					if (dummy_elp[j] != 0)
						dummy_elp[j] = GFMult(dummy_elp[j], (1 << j));
			}
			for (j = 1; j <= L[k_ttx2-1]; j++)
				reg[j] = GFMult(reg[j], dummy_elp[j]);

			for (i = nn-length+1; i <= nn; i++)
#endif
			{
				elp_sum = reg[0];
				for (j = 1; j <= L[k_ttx2-1]; j++)
				{
					if (reg[j] != 0)
					{ 	
						reg[j] = GFMult(reg[j], (1 << j));
						elp_sum ^= reg[j] ;
					}
				}
				
				if (!elp_sum)		// store root and error location number indices
				{ 
					root[count] = i;
					location[count] = nn - i ;
					count++ ;
				}
			}
			
			if (count == L[k_ttx2-1])    // Number of roots = degree of elp hence <= tt errors
			{	
				decode_flag = 1 ;
			}
			else	// Number of roots != degree of ELP => >tt errors and cannot solve
			{
				decode_flag = 0 ;
			}
		}
	}
}

int main(int argc,  char** argv)
{	
	int i, j ;
	int in_count, in_codeword;		// Input statistics
	int decode_success, decode_fail;		// Decoding statistics
	int	errpos[16], numerr;
	int	min_tmp, min_pos;
	int	pos_flag;

	long seed;
	time(&seed);
	srand(seed);
	
	fprintf(stderr, "# Binary BCH decoder.  Use -h for details.\n\n");
	mm = 13;
	tt = k_tt;
	kk = 4096;
	length = kk + mm * tt;
	nn = (int)pow(2, mm) - 1;
	
	// generate the Galois Field GF(2**mm)
	generate_gf() ;
	
	// Compute the generator polynomial and lookahead matrix for BCH code
	gen_poly() ;

	fprintf(stdout, "{# (m = %d, n = %d, k = %d, t = %d) Binary BCH code.}\n\n", mm, length, kk, tt) ;
	
	decode_success = 0; 
	decode_fail = 0;
	for(in_codeword = 1; in_codeword <= 10000; in_codeword++)
	{
		for (i = 0; i < kk/8; i++){
			data[i] = rand() & 0xFF;	//(rand() & 65536) >> 16;
		}
		encode_bch(data);		//encode data is high signacture, 0x87= 10000111
		
		//recd[] are the coefficients of c(x) = x**(length-k)*data(x) + b(x)
		for (i = 0; i < kk/8; i++)
			recd[i] = data[i];
		for (i = 0; i < (length - kk)/8; i++)
			recd[i+kk/8] = bb[i];
	
		numerr = rand() & 0x0F;
		
		for (i = 0; i < numerr; i++)
		{
			errpos[i] = rand() & 8191;
			while(errpos[i] >= length)
			{
				errpos[i] = rand() & 8191;
			}
			
			for(j=0; j<i; j++){
				if(errpos[i] == errpos[j]){
					break;
				}
			}
			
			if(j != i){
				if(i != 0)
					i--;
			}
		}
		
//		errpos[0] = 0;

		for (i = 0; i < numerr; i++)
		{
			min_tmp = errpos[i];
			min_pos = i;
			for(j = i; j < numerr; j++)
			{
				if(min_tmp > errpos[j])
				{
					min_pos = j;
					min_tmp = errpos[j];
				}
			}
			
			if(min_pos != i){
				errpos[min_pos] = errpos[i];
				errpos[i] = min_tmp;
			}
		}
		
		for (i = 0; i < numerr; i++)
			recd[errpos[i]/8] ^= (1 << (7- (errpos[i]&0x7)));

		decode_bch() ;
		
		if(numerr != 0){
			fprintf(stdout, "Occurs %3d Errors. location:", numerr) ;
			for (i = 0; i < numerr; i++)
				fprintf(stdout, "%5d", errpos[i]) ;	
			fprintf(stdout, "\n") ;
		}
		
		if ( decode_flag == 1 )
		{
			decode_success++ ;
			if (count == 0)
			{
				fprintf(stdout, "{ Codeword %d: No errors.}\n", in_codeword) ;
			}
			else
			{
				fprintf(stdout, "{ Codeword %d: %d errors found at location:", in_codeword, count) ;
				pos_flag = 0;
				for (i = 0; i < count ; i++) 
				{
					// Convert error location from systematic form to storage form 
					if (location[i] >= rr)
						location[i] = kk+rr - location[i] - 1;
					else
						location[i] = location[i] + kk;

					recd[location[i]/8] ^= (1 << (7- (location[i]&0x7)));		// Correct errors by flipping the error bit

					fprintf(stdout, " %5d", location[i]) ;
				}
				fprintf(stdout, "}\n");
			}
			
			if(0 != memcmp(data, recd, kk/8)){
				fprintf(stdout, "BCH_ERROR data error\n") ;
				fprintf(stderr, "BCH_ERROR data error\n") ;
			}

			if(numerr > 8){
				fprintf(stdout, "BCH_ERROR {Error Count is: %d, but correct it now!!}\n", numerr) ;
				fprintf(stderr, "BCH_ERROR {Error Count is: %d, but correct it now!!}\n", numerr) ;
			}

			for (i = 0; i < count; i++)
			{
				min_tmp = location[i];
				min_pos = i;
				for(j = i; j < count; j++){
					if(min_tmp > location[j]){
						min_pos = j;
						min_tmp = location[j];
					}
				}
				if(min_pos != i){
					location[min_pos] = location[i];
					location[i] = min_tmp;
				}
	
				if(errpos[i] != location[i]){
					pos_flag = 1;
					fprintf(stdout, "BCH_ERROR {Error Position decode!!!\n") ;
					fprintf(stderr, "BCH_ERROR {Error Position decode!!!\n") ;
					break;
				}
			}
		}
		else
		{
			decode_fail++ ;
			fprintf(stdout, "{ Codeword %d: Unable to decode! ERROR!}\n", in_codeword) ;
			if(numerr <= 8){
				fprintf(stdout, "BCH_ERROR {Error Count is: %d, but uncorrect it now!!}\n", numerr) ;
				fprintf(stderr, "BCH_ERROR {Error Count is: %d, but uncorrect it now!!}\n", numerr) ;
			}
		}
		// Convert decoded data into information data and parity checks
		
		fprintf(stdout, "\n\n");
		in_count = 0;
	}
	
	fprintf(stderr, "completely\n");
	
	return(0);
}


void encode_bch(int *pdata)
/*
* Compute redundacy bb[], the coefficients of b(x). The redundancy
* polynomial b(x) is the remainder after dividing x^(length-k)*data(x)
* by the generator polynomial g(x).
*/
{
/*
	register int    i, j;
	register int    feedback;
	
	for (i = 0; i < length - kk; i++)
		bb[i] = 0;
	for (i = kk - 1; i >= 0; i--) 
	{
		feedback = pdata[i] ^ bb[length - kk - 1];
		if (feedback != 0) 
		{
			for (j = length - kk - 1; j > 0; j--)
				if (gg[j] != 0)
					bb[j] = bb[j - 1] ^ feedback;
				else
					bb[j] = bb[j - 1];
				bb[0] = gg[0] && feedback;
		} 
		else 
		{
			for (j = length - kk - 1; j > 0; j--)
				bb[j] = bb[j - 1];
			bb[0] = 0;
		}
	}
*/
	register int    i, j;
	
	int		D[8];
	int		CRC[104];
	
	for (i = 0; i < length - kk; i++)
		bb[i] = 0;
	
	for(i=0; i < kk/8; i++)
	{
		//memcpy(D, &pdata[i*8], 8*sizeof(int));		//Convert bits to Byte... 
		for(j=0; j<8; j++){
			D[j] = (pdata[i] >> j) & 0x01;
		}

		//Parallel CRC 1Byte
		//Assign CRC[0...103] = .....;
		CRC[0] = bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[1] = bb[97] ^ bb[101] ^ D[5] ^ bb[100] ^ D[4] ^ D[1]  ;
		CRC[2] = bb[98] ^ bb[102] ^ D[6] ^ bb[101] ^ D[5] ^ D[2]  ;
		CRC[3] = bb[99] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[3]  ;
		CRC[4] = bb[96] ^ bb[99] ^ bb[103] ^ D[7] ^ D[3] ^ D[0]  ;
		CRC[5] = bb[97] ^ bb[100] ^ D[4] ^ D[1]  ;
		CRC[6] = bb[98] ^ bb[101] ^ D[5] ^ D[2] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[7] = bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[8] = bb[0] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2] ^ bb[97] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[9] = bb[1] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[103] ^ D[7] ^ D[0]  ;
		CRC[10] = bb[2] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[100] ^ D[4] ^ D[0]  ;
		CRC[11] = bb[3] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1]  ;
		CRC[12] = bb[4] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[13] = bb[5] ^ bb[99] ^ D[3] ^ bb[97] ^ bb[101] ^ D[5] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[14] = bb[6] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[99] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[15] = bb[7] ^ bb[99] ^ D[3] ^ bb[97] ^ bb[100] ^ bb[103] ^ D[7] ^ D[4] ^ D[1]  ;
		CRC[16] = bb[8] ^ bb[98] ^ bb[101] ^ D[5] ^ D[2] ^ bb[96] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[17] = bb[9] ^ bb[97] ^ D[1] ^ bb[96] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[18] = bb[10] ^ bb[98] ^ D[2] ^ bb[97] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[19] = bb[11] ^ bb[99] ^ D[3] ^ bb[98] ^ D[2]  ;
		CRC[20] = bb[12] ^ bb[100] ^ D[4] ^ bb[99] ^ D[3]  ;
		CRC[21] = bb[13] ^ bb[101] ^ D[5] ^ bb[100] ^ D[4]  ;
		CRC[22] = bb[14] ^ bb[102] ^ D[6] ^ bb[101] ^ D[5]  ;
		CRC[23] = bb[15] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[24] = bb[16] ^ bb[97] ^ bb[101] ^ D[5] ^ bb[100] ^ bb[103] ^ D[7] ^ D[4] ^ D[1]  ;
		CRC[25] = bb[17] ^ bb[98] ^ bb[102] ^ D[6] ^ bb[101] ^ D[5] ^ D[2]  ;
		CRC[26] = bb[18] ^ bb[99] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[3]  ;
		CRC[27] = bb[19] ^ bb[100] ^ bb[103] ^ D[7] ^ D[4]  ;
		CRC[28] = bb[20] ^ bb[101] ^ D[5] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[29] = bb[21] ^ bb[102] ^ D[6] ^ bb[97] ^ bb[101] ^ D[5] ^ bb[100] ^ D[4] ^ D[1]  ;
		CRC[30] = bb[22] ^ bb[103] ^ D[7] ^ bb[98] ^ bb[102] ^ D[6] ^ bb[101] ^ D[5] ^ D[2]  ;
		CRC[31] = bb[23] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[32] = bb[24] ^ bb[97] ^ bb[101] ^ D[5] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[33] = bb[25] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2]  ;
		CRC[34] = bb[26] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[103] ^ D[7] ^ D[0]  ;
		CRC[35] = bb[27] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[36] = bb[28] ^ bb[98] ^ D[2] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[99] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[37] = bb[29] ^ bb[99] ^ D[3] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2] ^ bb[97] ^ bb[100] ^ bb[103] ^ D[7] ^ D[4] ^ D[1]  ;
		CRC[38] = bb[30] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[103] ^ D[7] ^ D[3] ^ bb[98] ^ bb[101] ^ D[5] ^ D[2]  ;
		CRC[39] = bb[31] ^ bb[101] ^ D[5] ^ bb[96] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[40] = bb[32] ^ bb[97] ^ D[1] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[41] = bb[33] ^ bb[98] ^ D[2] ^ bb[97] ^ bb[101] ^ D[5] ^ bb[100] ^ bb[103] ^ D[7] ^ D[4] ^ D[1]  ;
		CRC[42] = bb[34] ^ bb[99] ^ D[3] ^ bb[98] ^ bb[102] ^ D[6] ^ bb[101] ^ D[5] ^ D[2]  ;
		CRC[43] = bb[35] ^ bb[96] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[44] = bb[36] ^ bb[97] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[45] = bb[37] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[46] = bb[38] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ D[0]  ;
		CRC[47] = bb[39] ^ bb[98] ^ D[2] ^ bb[97] ^ D[1] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[48] = bb[40] ^ bb[98] ^ D[2] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[103] ^ D[7] ^ D[0]  ;
		CRC[49] = bb[41] ^ bb[98] ^ D[2] ^ bb[97] ^ D[1] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[50] = bb[42] ^ bb[99] ^ D[3] ^ bb[98] ^ D[2] ^ bb[97] ^ bb[101] ^ D[5] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[51] = bb[43] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[52] = bb[44] ^ bb[97] ^ D[1] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[103] ^ D[7] ^ D[0]  ;
		CRC[53] = bb[45] ^ bb[98] ^ D[2] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[54] = bb[46] ^ bb[99] ^ D[3] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2] ^ bb[97] ^ bb[101] ^ D[5] ^ bb[100] ^ D[4] ^ D[1]  ;
		CRC[55] = bb[47] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[103] ^ D[7] ^ D[3] ^ bb[98] ^ bb[102] ^ D[6] ^ bb[101] ^ D[5] ^ D[2]  ;
		CRC[56] = bb[48] ^ bb[101] ^ D[5] ^ bb[96] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[57] = bb[49] ^ bb[102] ^ D[6] ^ bb[97] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[58] = bb[50] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[103] ^ D[7] ^ D[3] ^ D[0]  ;
		CRC[59] = bb[51] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ D[0]  ;
		CRC[60] = bb[52] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2] ^ bb[97] ^ D[1]  ;
		CRC[61] = bb[53] ^ bb[99] ^ bb[103] ^ D[7] ^ D[3] ^ bb[98] ^ D[2]  ;
		CRC[62] = bb[54] ^ bb[96] ^ D[0]  ;
		CRC[63] = bb[55] ^ bb[97] ^ D[1]  ;
		CRC[64] = bb[56] ^ bb[98] ^ D[2]  ;
		CRC[65] = bb[57] ^ bb[96] ^ bb[100] ^ D[4] ^ D[0]  ;
		CRC[66] = bb[58] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1]  ;
		CRC[67] = bb[59] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[68] = bb[60] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[103] ^ D[7] ^ D[0]  ;
		CRC[69] = bb[61] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2] ^ bb[97] ^ D[1]  ;
		CRC[70] = bb[62] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[103] ^ D[7] ^ D[0]  ;
		CRC[71] = bb[63] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[100] ^ D[4] ^ D[0]  ;
		CRC[72] = bb[64] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1]  ;
		CRC[73] = bb[65] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[74] = bb[66] ^ bb[99] ^ D[3] ^ bb[97] ^ bb[101] ^ D[5] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[75] = bb[67] ^ bb[100] ^ D[4] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2]  ;
		CRC[76] = bb[68] ^ bb[101] ^ D[5] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[103] ^ D[7] ^ D[0]  ;
		CRC[77] = bb[69] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[78] = bb[70] ^ bb[98] ^ bb[102] ^ D[6] ^ D[2] ^ bb[97] ^ bb[101] ^ D[5] ^ bb[100] ^ bb[103] ^ D[7] ^ D[4] ^ D[1]  ;
		CRC[79] = bb[71] ^ bb[99] ^ bb[103] ^ D[7] ^ D[3] ^ bb[98] ^ bb[102] ^ D[6] ^ bb[101] ^ D[5] ^ D[2]  ;
		CRC[80] = bb[72] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[3]  ;
		CRC[81] = bb[73] ^ bb[101] ^ D[5] ^ bb[100] ^ bb[103] ^ D[7] ^ D[4]  ;
		CRC[82] = bb[74] ^ bb[101] ^ D[5] ^ bb[96] ^ bb[100] ^ D[4] ^ bb[99] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[83] = bb[75] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1] ^ bb[96] ^ bb[99] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[84] = bb[76] ^ bb[98] ^ D[2] ^ bb[97] ^ D[1] ^ bb[96] ^ bb[99] ^ bb[103] ^ D[7] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[85] = bb[77] ^ bb[98] ^ D[2] ^ bb[97] ^ D[1] ^ bb[96] ^ bb[103] ^ D[7] ^ D[0]  ;
		CRC[86] = bb[78] ^ bb[99] ^ D[3] ^ bb[98] ^ D[2] ^ bb[97] ^ D[1]  ;
		CRC[87] = bb[79] ^ bb[98] ^ D[2] ^ bb[96] ^ D[0]  ;
		CRC[88] = bb[80] ^ bb[99] ^ D[3] ^ bb[97] ^ D[1]  ;
		CRC[89] = bb[81] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[90] = bb[82] ^ bb[99] ^ D[3] ^ bb[97] ^ bb[100] ^ D[4] ^ D[1]  ;
		CRC[91] = bb[83] ^ bb[98] ^ bb[101] ^ D[5] ^ D[2] ^ bb[96] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[92] = bb[84] ^ bb[99] ^ bb[102] ^ D[6] ^ D[3] ^ bb[97] ^ bb[100] ^ D[4] ^ D[1]  ;
		CRC[93] = bb[85] ^ bb[98] ^ bb[101] ^ D[5] ^ D[2] ^ bb[96] ^ bb[99] ^ bb[103] ^ D[7] ^ D[3] ^ D[0]  ;
		CRC[94] = bb[86] ^ bb[97] ^ D[1] ^ bb[96] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[95] = bb[87] ^ bb[98] ^ D[2] ^ bb[97] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[96] = bb[88] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[100] ^ D[4] ^ D[0]  ;
		CRC[97] = bb[89] ^ bb[99] ^ D[3] ^ bb[97] ^ bb[101] ^ D[5] ^ D[1]  ;
		CRC[98] = bb[90] ^ bb[98] ^ D[2] ^ bb[96] ^ bb[99] ^ bb[102] ^ D[6] ^ D[3] ^ D[0]  ;
		CRC[99] = bb[91] ^ bb[99] ^ D[3] ^ bb[97] ^ bb[100] ^ bb[103] ^ D[7] ^ D[4] ^ D[1]  ;
		CRC[100] = bb[92] ^ bb[98] ^ bb[101] ^ D[5] ^ D[2] ^ bb[96] ^ bb[99] ^ D[3] ^ D[0]  ;
		CRC[101] = bb[93] ^ bb[97] ^ D[1] ^ bb[96] ^ bb[102] ^ D[6] ^ D[0]  ;
		CRC[102] = bb[94] ^ bb[98] ^ D[2] ^ bb[97] ^ bb[103] ^ D[7] ^ D[1]  ;
		CRC[103] = bb[95] ^ bb[99] ^ D[3] ^ bb[98] ^ D[2]  ;
		
		//=====================================================
		
		memcpy(bb, CRC, 104*sizeof(int));		//bb[0...104] <= CRC[0...104];	Next Clock , Save the data to bb
	}

	//make bb to byte
	for(i=0; i<104/8; i++)
	{
		bb[i] = bb[i*8];
		for(j=1; j<8; j++)
		{
			bb[i] <<= 1;
			bb[i] |= bb[i*8+j];
		}
	}

}
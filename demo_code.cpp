//Title : Conformity Poses a Double-Edged Sword Effect on the Evolution of Cooperation within Heterogeneous Endowment Populations
//Authors: Xiaoyue Wang; Zhixue He; Lei Shi.
// email shi_lei65@hotmail.com (L.S.)

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <ctime>
#include <string.h>

using namespace std;
#define L 100
#define N L*L
#define RANDOMIZE   3145215
#define str_num  2
#define neig_num  8

/*************************** RNG procedures ****************************************/
#define NN 624
#define MM 397
#define MATRIX_A 0x9908b0df   /* constant vector a */
#define UPPER_MASK 0x80000000 /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff /* least significant r bits */
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define TEMPERING_SHIFT_U(y)  (y >> 11)
#define TEMPERING_SHIFT_S(y)  (y << 7)
#define TEMPERING_SHIFT_T(y)  (y << 15)
#define TEMPERING_SHIFT_L(y)  (y >> 18)

static unsigned long mt[NN]; /* the array for the state vector  */
static int mti=NN+1; /* mti==NN+1 means mt[NN] is not initialized */
void sgenrand(unsigned long seed)
{int i;
 for (i=0;i<NN;i++) {mt[i] = seed & 0xffff0000; seed = 69069 * seed + 1;
                     mt[i] |= (seed & 0xffff0000) >> 16; seed = 69069 * seed + 1;
  }
  mti = NN;
}
void lsgenrand(unsigned long seed_array[])
{ int i; for (i=0;i<NN;i++) mt[i] = seed_array[i]; mti=NN; }
double genrand() 
{
    unsigned long y;
    static unsigned long mag01[2]={0x0, MATRIX_A};
    if (mti >= NN) 
    {
        int kk;
        if (mti == NN+1) sgenrand(4357); 
        for (kk=0;kk<NN-MM;kk++) {
            y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);
            mt[kk] = mt[kk+MM] ^ (y >> 1) ^ mag01[y & 0x1];
        }
        for (;kk<NN-1;kk++) {
            y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);  
            mt[kk] = mt[kk+(MM-NN)] ^ (y >> 1) ^ mag01[y & 0x1];
        }
        y = (mt[NN-1]&UPPER_MASK)|(mt[0]&LOWER_MASK);
        mt[NN-1] = mt[MM-1] ^ (y >> 1) ^ mag01[y & 0x1];
        mti = 0;
    }  
    y = mt[mti++]; y ^= TEMPERING_SHIFT_U(y); y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
    y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C; y ^= TEMPERING_SHIFT_L(y);
    return y;  
}

double randf(){ return ( (double)genrand() * 2.3283064370807974e-10 ); }
long randi(unsigned long LIM){ return((unsigned long)genrand() % LIM); }

/********************** END of RNG ************************************/

int neighbors[N][neig_num];
int strategy[N];
int type[N]; 
int learn_rule[N];

double pm1[str_num][str_num];
double pm2[str_num][str_num];
double pm3[str_num][str_num];
double pm4[str_num][str_num];

double c,cr,cp,alpha,rho,phi,f;
double K1 = 10; 
double K2 = 10;


int temp_net[L+4][L+4];
void define_grid(void)
{
	int intera = 1;
	int count=0;
	for(int i=intera; i<L+intera; i++){
		for(int j=intera; j<L+intera; j++){
			temp_net[i][j] = count;
			count ++;
		}
	}
	
	int temp_x;
	for(int i=0; i<intera; i++){
		for(int j=intera; j<L+intera; j++){
			temp_net[i][j] = temp_net[i+L][j];
			temp_net[i+L+intera][j] = temp_net[intera+i][j];
			temp_net[j][i] = temp_net[j][i+L];
			temp_net[j][i+L+intera] = temp_net[j][intera+i];
		}
	}
	for(int i=0; i<intera; i++){
		for(int j=0; j<intera; j++){
			temp_net[i][j]  = temp_net[i][j+L];
			temp_net[i][j+L+intera]  = temp_net[i][j+intera];
			temp_net[i+L+intera][j]  = temp_net[i+L+intera][j+L];
			temp_net[i+L+intera][j+L+intera]  = temp_net[i+L+intera][j+intera];
		}
	}
	int center;
	int temp_node;
	int neig_count;
	for(int i=intera; i<L+intera; i++){
		for(int j=intera; j<L+intera; j++){
			center = temp_net[i][j];
			neig_count = 0;
			for(int new_i=i-intera; new_i<i+intera+1; new_i++){
				for(int new_j=j-intera; new_j<j+intera+1; new_j++){
					temp_node = temp_net[new_i][new_j];
					if(temp_node != center){
						neighbors[center][neig_count] = temp_node;
						neig_count ++;
					}
				}
			}
		}
	}
}

void init_game(void)
{
	define_grid();
	
	cp =  1 / ( alpha * phi + 1.0 );
	cr = (1.0 + phi) * cp   ;
	
	double tm1[2][2] = {
		{ f * cr  ,  f * cr / 2.0  },
		{  f * cr / 2.0 + cr , 0.0 + cr},	
	};
	double tm2[2][2] = {
		{ f * ( cr + cp ) / 2.0 ,  f * cr / 2.0},
		{  f * cp / 2.0 + cr, 0.0 + cr },	
	};
	double tm3[2][2] = {
		{ f * ( cr + cp ) / 2.0 ,  f * cp / 2.0 },
		{  f * cr / 2.0 + cp, 0.0 + cp},	
	};
	double tm4[2][2] = {
		{ f * cp ,  f * cp / 2.0 },
		{  f * cp / 2.0 + cp , 0.0 + cp},	
	};
	
	memcpy( pm1, tm1, sizeof(tm1) );
	memcpy( pm2, tm2, sizeof(tm2) );
	memcpy( pm3, tm3, sizeof(tm3) );
	memcpy( pm4, tm4, sizeof(tm4) );
	
	
	for (int i=0; i<N; i++){
		type[i] = ( randf() < alpha  )? 0:1;
		learn_rule[i] = ( randf() < rho  )? 0:1;
		strategy[i] = randi(str_num);
	}
}


double cal_payoff(int center)
{
	int x_str = strategy[center];
	int center_type = type[center];
	double pay=0;
	int neig;
	
	if(center_type == 0){
		for(int i=0; i<neig_num; i++){
			neig = neighbors[center][i];
			if(type[neig] == 0) pay += pm1[x_str][strategy[neig]];
			else if (type[neig] == 1) pay += pm2[x_str][strategy[neig]];
		}
	}
	else if(center_type == 1){
		for(int i=0; i<neig_num; i++){
			neig = neighbors[center][i];
			if(type[neig] == 0) pay += pm3[x_str][strategy[neig]];
			else if (type[neig] == 1) pay += pm4[x_str][strategy[neig]];
		}
	}

	return pay;
}

void learn_comforty(int center){
	
	int half_mark = (neig_num) / 2;
	int center_str = strategy[center];
	int same_strategy_num = 0;
	
	for(int i=0; i<neig_num; i++){
		if( center_str == strategy[ neighbors[center][i] ] ) same_strategy_num ++;
	}
	
	double prob = (double)  1 / ( 1 + exp(   ( same_strategy_num - half_mark ) * K2 ) );
	
	if( randf() < prob ){
		strategy[center] = (center_str == 0)? 1:0;
	}
} 

void learn_fermi(int center)
{
	int neig = neighbors[center][randi(neig_num)];
	while(type[neig] == -1) neig = neighbors[center][randi(neig_num)];
	
	double center_pay = cal_payoff(center);
	double neig_pay = cal_payoff(neig);

	double prob = (double) 1 / ( 1 + exp( ( center_pay - neig_pay ) * K1  ) );
	if( randf() < prob ) strategy[center] = strategy[neig];	
	
}

void main_process( void )
{
	int center;
	for(int i=0;i<N;i++){
		center = randi(N);
		if(learn_rule[center] == 0)  learn_comforty(center);
		else  learn_fermi(center);
	}
}

double data_out[3];
void cal_data(void){
	int stra_count[3]={0};
	int type_count[2]={0};
	for(int i=0; i<N; i++){
		if(strategy[i] == 0){
			stra_count[0] ++;
			stra_count[type[i]+1] ++;
		}
		type_count[type[i]] ++;
	}
	
	memset(data_out, 0, sizeof(data_out));
	data_out[0] = (double) stra_count[0] / (N);
	if(type_count[0] != 0) data_out[1] = (double) stra_count[1] / type_count[0];
	if(type_count[1] != 0) data_out[2] = (double) stra_count[2] / type_count[1];
}

int main(void) 
{
	sgenrand(time(0));

	int MCS = 100000;
	
	alpha = 0.2;
	f = 1.9;
	
	rho = 0.2;
	phi = 5.0;


	printf("alpha = %f, f = %f, rho = %f, phi = %f  ",alpha,f,rho,phi);
	init_game();
	
	for(int i=0; i<MCS; i++){
		
		main_process();
	}
	cal_data();
	printf("FC = %f , rich FC = %f  , poor FC = %f \n", data_out[0], data_out[1], data_out[2]);

	return 0; 
}




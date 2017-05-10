#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef struct _matrix_elem_t
{
	unsigned int column;
	double elem;
	struct _matrix_elem_t *next;
} matrix_elem;

typedef struct _sparse_matrix_t
{
	struct _matrix_elem_t *row;
} sparse_matrix;
/*
The elements of the sparse matrix are stored in link tables.
*/
#define MAX_ITER_TIMES 100000
#define COEFF_ERR -2
#define NOT_CONVERGE -1
#define SOLVED 0
#define INVALID_MAX_SIZE -1
#define INVALID_LIMIT -2
#define INVALID_STEP -3
#define UNEXPECTED_EOF -4
#define PARSE_OK 0
#define SOR 0
#define SSOR 1
#define CG 2
#define SSOR_PCG 3
#define ELEM_ALLOC_AND_ASSIGN(HEAD,CUR,NUM,VALUE) \
{\
	if(CUR==NULL)\
	{\
		HEAD=CUR=(matrix_elem *)allocmem(sizeof(matrix_elem));\
	}\
	else\
	{\
		CUR->next=(matrix_elem *)allocmem(sizeof(matrix_elem));\
		CUR=CUR->next;\
	}\
	CUR->column=NUM;\
	CUR->elem=VALUE;\
}
FILE *config_file=NULL;
FILE *output_file=NULL;
double factor_1=0.5;
double factor_2=1.5;
unsigned int method=SOR;
static void *allocmem(unsigned int size)
{
	/*
	If the machine just runs out of memory, send an error then terminate the program.
	*/
	void *ptomem=calloc(size,1);
	if(ptomem==NULL)
	{
		printf("Error: Memory limit exceeded.\n");
		exit(-1);
	}
	return ptomem;
}
static void destroy_sparse_matrix(sparse_matrix *matrix,int dim)
{
	/*
	This function is used to destroy a sparse matrix.
	*/
	int count;
	matrix_elem *cur_col,*pre_col;
	for(count=0;count<dim;count++)
	{
		cur_col=matrix[count].row;
		while(cur_col!=NULL)
		{
			pre_col=cur_col;
			cur_col=cur_col->next;
			free(pre_col);
		}
	}
	free(matrix);
	return;
}
static int gen_matrix(unsigned int max_size,double step_len,double *source,double *bound_cond,sparse_matrix **coeff_matrix,double **vector)
{
	/*
	Generating the coefficient matrix.
	*/
	sparse_matrix *cur=NULL;
	matrix_elem *cur_col=NULL;
	double sum;
	unsigned int index_1,index_2,index_3,bound_cond_num,square;
	int pos=0;
	if(max_size==0) return -1;
	square=max_size*max_size;
	*vector=(double *)allocmem(sizeof(double)*(max_size*max_size*max_size+1));
	cur=*coeff_matrix=(sparse_matrix *)allocmem(sizeof(sparse_matrix)*(max_size*max_size*max_size+1));	
	for(index_1=0,bound_cond_num=0;index_1<max_size;index_1++)
	{
		for(index_2=0;index_2<max_size;index_2++)
		{
			for(index_3=0;index_3<max_size;index_3++)
			{
				cur->row=NULL;
				sum=0;
				cur_col=NULL;
				/*
				(f(i-1,j,k)+f(i,j-1,k)+f(i,j,k-1)+f(i,j,k+1)+f(i,j+1,k)+f(i+1,j,k)-6f(i,j,k))/(step*step)=source(i,j,k)
				Each term on the LHS is either an unknown to be solved, or given by the boundary condition. If the corresponding index is 0 or max_size-1, the point is on the boundary.
				*/
				if(index_1>0)
				{
					ELEM_ALLOC_AND_ASSIGN(cur->row,cur_col,(index_1-1)*square+index_2*max_size+index_3,1);
				}
				else sum+=bound_cond[bound_cond_num++];
				if(index_2>0)
				{
					ELEM_ALLOC_AND_ASSIGN(cur->row,cur_col,index_1*square+(index_2-1)*max_size+index_3,1);				
				}
				else sum+=bound_cond[bound_cond_num++];
				if(index_3>0)
				{
					ELEM_ALLOC_AND_ASSIGN(cur->row,cur_col,index_1*square+index_2*max_size+index_3-1,1);				
				}
				else sum+=bound_cond[bound_cond_num++];
				ELEM_ALLOC_AND_ASSIGN(cur->row,cur_col,index_1*square+index_2*max_size+index_3,-6);	
				if(index_3<max_size-1)
				{
					ELEM_ALLOC_AND_ASSIGN(cur->row,cur_col,index_1*square+index_2*max_size+index_3+1,1);				
				}
				else sum+=bound_cond[bound_cond_num++];
				if(index_2<max_size-1)
				{
					ELEM_ALLOC_AND_ASSIGN(cur->row,cur_col,index_1*square+(index_2+1)*max_size+index_3,1);
				}
				else sum+=bound_cond[bound_cond_num++];
				if(index_1<max_size-1)
				{
					ELEM_ALLOC_AND_ASSIGN(cur->row,cur_col,(index_1+1)*square+index_2*max_size+index_3,1);
				}
				else sum+=bound_cond[bound_cond_num++];
				(*vector)[index_1*square+index_2*max_size+index_3]=step_len*step_len*source[index_1*square+index_2*max_size+index_3]+sum;
				cur_col=cur->row;
				cur++;
			}
		}
	}
	return 0;
}
static int check_and_covert_coeff(sparse_matrix *coeff_matrix,unsigned int dim,sparse_matrix **iter_matrix,double *vector,double **b_vector,double limit)
{
	/*
	Convert the coefficient matrix to SOR iteration matrix. This helps reduce the time consumed in the iteration but, in turn, increases the memory consumption.
	*/
	sparse_matrix *cur=NULL;
	matrix_elem *ptocolumn=NULL,*cur_col=NULL;
	unsigned int row_num=0;
	int has_err=1;
	double div=0;
	*b_vector=(double *)allocmem(sizeof(double)*(dim+1));
	cur=*iter_matrix=(sparse_matrix *)allocmem(sizeof(sparse_matrix)*(dim+1));
	for(row_num=0;row_num<dim;row_num++)
	{
		ptocolumn=coeff_matrix->row;
		has_err=1;
		/*
		Find the diagonal elements in the matrix.
		*/
		while(ptocolumn!=NULL)
		{
			if(ptocolumn->column>row_num)
			{
				has_err=1;
				break;
			}
			else if(ptocolumn->column==row_num)
			{
				div=ptocolumn->elem;
				if((div>limit)||(div<-limit)) has_err=0;
				else has_err=1;
				break;
			}
			ptocolumn=ptocolumn->next;
		}
		if(has_err)
		{
			/*
			If any of the diagonal element is zero or a very small number (compared with the iteration accuracy), the equations cannot be solved.
			*/
			destroy_sparse_matrix(*iter_matrix,dim);
			*iter_matrix=NULL;
			free(*b_vector);
			*b_vector=NULL;
			return -1;
		}
		ptocolumn=coeff_matrix->row;
		cur_col=NULL;
		while(ptocolumn!=NULL)
		{
			/*
			Select the non-diagonal elements. Divide them by the diagonal element. Put these elements into the new matrix
			*/
			if(ptocolumn->column!=row_num)
			{
				ELEM_ALLOC_AND_ASSIGN(cur->row,cur_col,ptocolumn->column,ptocolumn->elem/div);
			}
			ptocolumn=ptocolumn->next;
		}
		(*b_vector)[row_num]=-vector[row_num]/div;
		coeff_matrix++;
		cur++;
	}
	return 0;
}
static int sor_solve_eq(sparse_matrix *coeff_matrix,unsigned int dim,double *vector,double **ptosolu,double limit)
{
	sparse_matrix *iter_matrix,*ptorow;
	matrix_elem *ptocolumn;
	unsigned register row_num;
	double *b_vector;
	double *solution;
	double dis;
	unsigned int iter_times;
	double sum,cur;
	int todo=0;
	time_t start,end;
	start=clock();
	if(check_and_covert_coeff(coeff_matrix,dim,&iter_matrix,vector,&b_vector,limit))
	{
		return COEFF_ERR;
	}
	solution=(double *)allocmem((dim+1)*sizeof(double));
	for(iter_times=0;iter_times<MAX_ITER_TIMES;iter_times++)
	{
		ptorow=iter_matrix;
		todo=0;
		for(row_num=0;row_num<dim;row_num++)
		{
			ptocolumn=ptorow->row;
			/*
			sum=x(k)[0]*A[i][0]+x(k)[1]*A[i][1]+...+x(k-1)[n+1]*A[i][n+1]...
			*/
			sum=0;			
			while(ptocolumn!=NULL)
			{
				sum+=solution[ptocolumn->column]*ptocolumn->elem;
				ptocolumn=ptocolumn->next;
			}
			sum=b_vector[row_num]-sum;
			cur=solution[row_num];
			if(!todo)
			{
				dis=(cur-sum);
				if(dis>limit||dis<-limit) todo=1;
			}
			/*
			x(k)[n]=x(k)[n]*(1-r)+sum*r
			*/
			solution[row_num]=sum*factor_2-cur*factor_1;
			ptorow++;
		}		
		if(!todo) break;
	}
	destroy_sparse_matrix(iter_matrix,dim);
	free(b_vector);
	end=clock();
	if(iter_times>=MAX_ITER_TIMES)
	{
		free(solution);
		*ptosolu=NULL;
		return NOT_CONVERGE;
	}
	else
	{
		printf("After iterated %d times for %f seconds with SOR method...\n",iter_times,(double)(end-start)/CLOCKS_PER_SEC);
		*ptosolu=solution;
		return SOLVED;
	}
}
static ssor_solve_eq(sparse_matrix *coeff_matrix,unsigned int dim,double *vector,double **ptosolu,double limit)
{
	sparse_matrix *iter_matrix,*ptorow;
	matrix_elem *ptocolumn;
	unsigned register row_num;
	double *b_vector;
	double *solution;
	double dis;
	unsigned int iter_times;
	double sum,cur;
	int todo=0;
	time_t start,end;
	start=clock();
	if(check_and_covert_coeff(coeff_matrix,dim,&iter_matrix,vector,&b_vector,limit))
	{
		return COEFF_ERR;
	}
	solution=(double *)allocmem((dim+1)*sizeof(double));
	for(iter_times=0;iter_times<MAX_ITER_TIMES;)
	{
		ptorow=iter_matrix;
		row_num=0;
		todo=0;
		for(row_num=0;row_num<dim;row_num++)
		{
			ptocolumn=ptorow->row;
			/*
			sum=x(k)[0]*A[i][0]+x(k)[1]*A[i][1]+...+x(k-1)[n+1]*A[i][n+1]...
			*/
			sum=0;
			while(ptocolumn!=NULL)
			{
				sum+=solution[ptocolumn->column]*ptocolumn->elem;
				ptocolumn=ptocolumn->next;
			}
			sum=b_vector[row_num]-sum;
			cur=solution[row_num];
			if(!todo)
			{
				dis=(cur-sum);
				if(dis>limit||dis<-limit) todo=1;
			}
			/*
			x(k+1/2)[n]=x(k)[n]*(1-r)+sum*r
			*/
			solution[row_num]=sum*factor_2-cur*factor_1;
			ptorow++;
		}
		if(!todo) break;
		iter_times++;
		todo=0;
		for(ptorow--,row_num--;row_num>=0;row_num--)
		{
			ptocolumn=ptorow->row;
			/*
			sum=x(k+1/2)[0]*A[i][0]+x(k)[1]*A[i][1]+...+x(k+1)[n+1]*A[i][n+1]...
			*/
			sum=0;
			while(ptocolumn!=NULL)
			{
				sum+=solution[ptocolumn->column]*ptocolumn->elem;
				ptocolumn=ptocolumn->next;
			}
			sum=b_vector[row_num]-sum;
			cur=solution[row_num];
			if(!todo)
			{
				dis=cur-sum;
				if(dis>limit||dis<-limit) todo=1;
			}
			/*
			x(k+1)[n]=x(k+1/2)[n]*(1-r)+sum*r
			*/
			solution[row_num]=sum*factor_2-cur*factor_1;
			if(row_num==0) break;
			ptorow--;
		}
		if(!todo) break;
		iter_times++;
	}
	destroy_sparse_matrix(iter_matrix,dim);
	free(b_vector);
	end=clock();
	if(iter_times>=MAX_ITER_TIMES)
	{
		free(solution);
		*ptosolu=NULL;
		return NOT_CONVERGE;
	}
	else
	{
		printf("After iterated %d times for %f seconds with SSOR method...\n",iter_times,(double)(end-start)/CLOCKS_PER_SEC);
		*ptosolu=solution;
		return SOLVED;
	}
}
static cg_solve_eq(sparse_matrix *coeff_matrix,unsigned int dim,double *b_vector,double **ptosolu,double limit)
{
	double *solution,*p_vector,*res;
	unsigned register iter_times;
	unsigned register row_num;
	int todo=0;
	sparse_matrix *ptorow;
	matrix_elem *ptocolumn;
	double sum,old_sum;
	double inner_product;
	double step;
	double num;
	time_t start,end;
	start=clock();
	solution=(double *)allocmem(sizeof(double)*(dim+1));
	p_vector=(double *)allocmem(sizeof(double)*(dim+1));
	res=(double *)allocmem(sizeof(double)*(dim+1));
	/*
	p(0)=res(0)=b
	sum=(res(0),res(0))
	*/
	for(row_num=0,sum=0;row_num<dim;row_num++)
	{
		num=p_vector[row_num]=res[row_num]=b_vector[row_num];
		sum+=num*num;
	}
	for(iter_times=0;iter_times<MAX_ITER_TIMES;iter_times++)
	{
		/*
		inner_product=(p,-A*p)
		*/
		inner_product=0;
		ptorow=coeff_matrix;
		for(row_num=0;row_num<dim;row_num++)
		{
			ptocolumn=ptorow->row;
			num=p_vector[row_num];
			while(ptocolumn)
			{
				inner_product-=ptocolumn->elem*p_vector[ptocolumn->column]*num;
				ptocolumn=ptocolumn->next;
			}
			ptorow++;
		}
		/*
		step=sum/inner_product
		x(k+1)=x(k)+step*p(k)
		*/
		step=sum/inner_product;
		todo=0;
		for(row_num=0;row_num<dim;row_num++)
		{
			solution[row_num]+=num=step*p_vector[row_num];
			if(!todo)
			{
				if(num>limit||num<-limit) todo=1;
			}
		}
		if(!todo) break;
		/*
		oldsum=sum
		res(k+1)=res(k)-(-A)*p*step
		sum=(res(k+1),res(k+1))
		step=sum/oldsum
		*/
		old_sum=sum;
		sum=0;
		ptorow=coeff_matrix;
		for(row_num=0;row_num<dim;row_num++)
		{
			ptocolumn=ptorow->row;
			num=0;
			while(ptocolumn)
			{
				num-=ptocolumn->elem*p_vector[ptocolumn->column];
				ptocolumn=ptocolumn->next;
			}
			num=res[row_num]-num*step;
			sum+=num*num;
			res[row_num]=num;
			ptorow++;
		}
		step=sum/old_sum;
		/*
		p(k+1)=p(k)*step+res(k)
		*/
		for(row_num=0;row_num<dim;row_num++)
		{
			p_vector[row_num]=p_vector[row_num]*step+res[row_num];
		}
	}
	end=clock();
	free(p_vector);
	free(res);
	if(iter_times>=MAX_ITER_TIMES)
	{
		free(solution);
		*ptosolu=NULL;
		return NOT_CONVERGE;
	}
	else
	{
		printf("After iterated %d times for %f seconds with CG method...\n",iter_times,(double)(end-start)/CLOCKS_PER_SEC);
		*ptosolu=solution;
		return SOLVED;
	}
}
static ssor_pcg_solve_eq(sparse_matrix *coeff_matrix,unsigned int dim,double *b_vector,double **ptosolu,double limit)
{
	double *solution,*p_vector,*res,*z_vector;
	unsigned register iter_times;
	unsigned register row_num;
	int todo=0;
	matrix_elem *ptocolumn;
	double sum,old_sum;
	double inner_product;
	double step;
	double num;
	double div;
	time_t start,end;
	start=clock();
	solution=(double *)allocmem(sizeof(double)*(dim+1));
	p_vector=(double *)allocmem(sizeof(double)*(dim+1));
	z_vector=(double *)allocmem(sizeof(double)*(dim+1));
	res=(double *)allocmem(sizeof(double)*(dim+1));
	/*
	res(0)=b
	p(0)=z(0)=M*b (M is the ssor iteration matrix. Calculating z(0)=M*b is equivalant to doing ssor iteration for A*z(0)=b )
	sum=(res(0),z(0))
	*/
	for(row_num=0,sum=0;row_num<dim;row_num++)
	{
		res[row_num]=b_vector[row_num];
	}
	for(row_num=0;row_num<dim;row_num++)
	{
		ptocolumn=coeff_matrix[row_num].row;
		num=0;
		div=0;
		while(ptocolumn!=NULL)
		{
			if(ptocolumn->column==row_num)
			{
				div=-ptocolumn->elem;
			}
			else num-=z_vector[ptocolumn->column]*ptocolumn->elem;
			ptocolumn=ptocolumn->next;
		}
		z_vector[row_num]=((res[row_num]-num)/div)*factor_2;
	}
	sum=0;
	for(row_num--;row_num>=0;row_num--)
	{
		ptocolumn=coeff_matrix[row_num].row;
		num=0;
		div=0;
		while(ptocolumn!=NULL)
		{
			if(ptocolumn->column==row_num)
			{
				div=-ptocolumn->elem;
			}
			else num-=z_vector[ptocolumn->column]*ptocolumn->elem;
			ptocolumn=ptocolumn->next;
		}
		p_vector[row_num]=z_vector[row_num]=((res[row_num]-num))/div*factor_2-z_vector[row_num]*factor_1;
		sum+=z_vector[row_num]*res[row_num];
		if(row_num==0) break;
	}
	for(iter_times=0;iter_times<MAX_ITER_TIMES;iter_times++)
	{
		/*
		inner_product=(p(k),-A*p(k))
		*/
		inner_product=0;
		for(row_num=0;row_num<dim;row_num++)
		{
			ptocolumn=coeff_matrix[row_num].row;
			num=p_vector[row_num];
			while(ptocolumn)
			{
				inner_product-=ptocolumn->elem*p_vector[ptocolumn->column]*num;
				ptocolumn=ptocolumn->next;
			}
		}
		/*
		step=sum/inner_product
		x(k+1)=x(k)+step*p(k)
		*/
		step=sum/inner_product;
		todo=0;
		for(row_num=0;row_num<dim;row_num++)
		{
			solution[row_num]+=num=step*p_vector[row_num];
			if(!todo)
			{
				if(num>limit||num<-limit) todo=1;
			}
		}
		if(!todo) break;
		/*
		oldsum=sum
		res(k+1)=res(k)-(-A)*p*step
		z(k+1)=M*res(k+1) (Doing ssor iteration for A*z(k+1)=res(k+1))
		sum=(z(k+1),res(k+1))
		step=sum/oldsum
		*/
		old_sum=sum;
		for(row_num=0;row_num<dim;row_num++)
		{
			ptocolumn=coeff_matrix[row_num].row;
			num=0;
			while(ptocolumn)
			{
				num-=ptocolumn->elem*p_vector[ptocolumn->column];
				ptocolumn=ptocolumn->next;
			}
			z_vector[row_num]=0;
			res[row_num]=res[row_num]-num*step;
		}
		for(row_num=0;row_num<dim;row_num++)
		{
			ptocolumn=coeff_matrix[row_num].row;
			num=0;
			div=0;
			while(ptocolumn!=NULL)
			{
				if(ptocolumn->column==row_num)
				{
					div=-ptocolumn->elem;
				}
				else num-=z_vector[ptocolumn->column]*ptocolumn->elem;
				ptocolumn=ptocolumn->next;
			}
			z_vector[row_num]=((res[row_num]-num)/div)*factor_2;
		}
		sum=0;
		for(row_num--;row_num>=0;row_num--)
		{
			ptocolumn=coeff_matrix[row_num].row;
			num=0;
			div=0;
			while(ptocolumn!=NULL)
			{
				if(ptocolumn->column==row_num)
				{
					div=-ptocolumn->elem;
				}
				else num-=z_vector[ptocolumn->column]*ptocolumn->elem;
				ptocolumn=ptocolumn->next;
			}
			z_vector[row_num]=((res[row_num]-num)/div)*factor_2-z_vector[row_num]*factor_1;
			sum+=z_vector[row_num]*res[row_num];
			if(row_num==0) break;
		}
		step=sum/old_sum;
		/*
		p(k+1)=p(k)*step+res(k)
		*/
		for(row_num=0;row_num<dim;row_num++)
		{
			p_vector[row_num]=p_vector[row_num]*step+z_vector[row_num];
		}
	}
	end=clock();
	free(p_vector);
	free(res);
	free(z_vector);
	if(iter_times>=MAX_ITER_TIMES)
	{
		free(solution);
		*ptosolu=NULL;
		return NOT_CONVERGE;
	}
	else
	{
		printf("After iterated %d times for %f seconds with SSOR-PCG method...\n",iter_times,(double)(end-start)/CLOCKS_PER_SEC);
		*ptosolu=solution;
		return SOLVED;
	}
}
static int parse_file(FILE *data_file,double **source,double **boundary_cond,int *max_size,double *limit,double *step)
{
	int count=0;
	int num=0;
	int bound_num=0;
	double *ptosource=NULL;
	double *ptobound=NULL;
	double temp;
	*max_size=0;
	*limit=0;
	*source=NULL;
	/*
	Get number of grids on each side from the data file.
	*/
	if(fscanf(data_file,"%d",max_size)<=0) return INVALID_MAX_SIZE;
	if(*max_size<=1) return INVALID_MAX_SIZE;
	/*
	Get iteration accuracy from the data file.
	*/
	if(fscanf(data_file,"%lf",limit)<=0) return INVALID_LIMIT;
	if(*limit<=0) return INVALID_LIMIT;
	/*
	Get step length from the data file.
	*/
	if(fscanf(data_file,"%lf",step)<=0) return INVALID_STEP;
	if(*step<=0) return INVALID_STEP;
	/*
	Calculate number of grids and boundary conditions.
	*/
	num=(*max_size)*(*max_size)*(*max_size);
	bound_num=3*8+(*max_size-2)*2*12+(*max_size-2)*(*max_size-2)*6;
	ptosource=(double *)allocmem(sizeof(double)*(num+1));
	ptobound=(double *)allocmem(sizeof(double)*(bound_num+1));
	for(count=0;count<bound_num;count++)
	{
		/*
		Get boundary conditions.
		*/
		if(feof(data_file))
		{
			free(ptosource);
			free(ptobound);
			*source=NULL;
			*boundary_cond=NULL;
			return UNEXPECTED_EOF;
		}
		if(fscanf(data_file,"%lf",&temp)<=0)
		{
			free(ptosource);
			free(ptobound);
			*source=NULL;
			*boundary_cond=NULL;
			return UNEXPECTED_EOF;
		}
		ptobound[count]=temp;
	}
	for(count=0;count<num;count++)
	{
		/*
		Get values of the source function on each point.
		*/
		if(feof(data_file))
		{
			free(ptosource);
			free(ptobound);
			*source=NULL;
			*boundary_cond=NULL;
			return UNEXPECTED_EOF;
		}
		if(fscanf(data_file,"%lf",&temp)<=0)
		{
			free(ptosource);
			free(ptobound);
			*source=NULL;
			*boundary_cond=NULL;
			return UNEXPECTED_EOF;
		}
		ptosource[count]=temp;
	}
	*source=ptosource;
	*boundary_cond=ptobound;
	return PARSE_OK;
}
static int parsearg(int argc,char **argv)
{
	int hasf=0,haso=0;
	int i=0;
	double fac;
	for(i=1;i<argc;i++)
	{
		if(argv[i][0]=='-'&&(argv[i+1]&&argv[i+1][0]!='-'))
		{
			switch(argv[i][1])
			{
			case 'f':
				config_file=fopen(argv[i+1],"r+");
				if(config_file==NULL) 
				{
					printf("Invalid data file: %s\n",argv[i+1]);
					return -2;
				}
				hasf=1;
				i++;
				break;
			case 'o':
				output_file=fopen(argv[i+1],"w+");
				if(config_file==NULL) 
				{
					printf("Invalid output file: %s\n",argv[i+1]);
					return -3;
				}
				haso=1;
				i++;
				break;
			case 'r':
				if(sscanf(argv[i+1],"%lf",&fac)<=0)
				{
					printf("Invalid relaxation factor: \"%s\" Relaxtion factor must be a number.\n",argv[i+1]);
					return -4;
				}
				if(fac>2||fac<0)
				{
					printf("Invalid relaxation factor: \"%s\" Relaxation factor must be larger than 0 and smaller than 2.\n",argv[i+1]);
					return -4;
				}
				factor_2=fac;
				factor_1=fac-1;
				break;
			case 'm':
				switch(atoi(argv[i+1]))
				{
				case 0:
					method=SOR;
					break;
				case 1:
					method=SSOR;
					break;
				case 2:
					method=CG;
					break;
				case 3:
					method=SSOR_PCG;
					break;
				default:
					printf("Invalid method factor: \"%s\" Method should be 0, 1, 2 or 3.\n",argv[i+1]);
					return -5;
				}
				break;
			}
		}
	}
	if(hasf&&haso) return 0;
	else return -1;
}
static void printusage(char *arg)
{
	printf("Usage: %s -f data_file_name -o output_file_name [-r relaxation factor -m method]\n",arg);
	printf("-f: The name of the data file.\n");
	printf("-o: The name of the output file.\n");
	printf("-r: The relaxation factor for SOR/SSOR/SSOR-PCG iteration. Default: 1.5\n");
	printf("-m: The relaxation method. \"0\"->\"SOR\" \"1\"->\"SSOR\" \"2\"->\"CG\" \"3\"->\"SSOR-PCG\" Default: 0\n");
	printf("The first three numbers in the data file stand for the number of grids on one side, the iteration accuracy, and the step length, respectively.\n");
	printf("Then follows all the boundary conditions and values of the source function on all points.\n");
	return;
}
void printsolu(FILE *data_file,double *solution,unsigned int max_size)
{
	unsigned int index_1=0,index_2=0,index_3=0;
	unsigned int count=0;
	for(index_1=0;index_1<max_size;index_1++)
	{
		for(index_2=0;index_2<max_size;index_2++)
		{
			for(index_3=0;index_3<max_size;index_3++)
			{
				fprintf(data_file,"%lf ",solution[count]);
				count++;
			}
			fprintf(data_file,"\n");
		}
		fprintf(data_file,"\n");
	}
	return;
}
int main(int argc,char **argv)
{
	double *source_func;
	int max_size;
	int result=0;
	double accuracy;
	double step;
	double *solution;
	sparse_matrix *coeff_matrix;
	double *vector;
	double *boundary;
	if(parsearg(argc,argv)!=0)
	{
		printusage(argv[0]);
		return -1;
	}
	switch(parse_file(config_file,&source_func,&boundary,&max_size,&accuracy,&step))
	{
	case INVALID_MAX_SIZE:
		printf("ERROR: Invalid max size.\n");
		printusage(argv[0]);
		return -2;
		break;
	case INVALID_LIMIT:
		printf("ERROR: Invalid limit.\n");
		printusage(argv[0]);
		return -2;
		break;
	case INVALID_STEP:
		printf("ERROR: Invalid step length.\n");
		printusage(argv[0]);
		return -2;
		break;
	case UNEXPECTED_EOF:
		printf("ERROR: Unexpected end of data file, or there are some invalid characters in the data file.\n");
		printusage(argv[0]);
		return -2;
		break;
	}
	fclose(config_file);
	if(gen_matrix(max_size,step,source_func,boundary,&coeff_matrix,&vector)!=0)
	{
		free(source_func);
		free(boundary);
		fclose(output_file);
		printf("Error: An unexpected error happened. This means noting but there's a bug in this program.\n");
		return -2;
	}
	free(boundary);
	free(source_func);
	switch(method)
	{
	case SOR:
		result=sor_solve_eq(coeff_matrix,max_size*max_size*max_size,vector,&solution,accuracy);
		break;
	case SSOR:
		result=ssor_solve_eq(coeff_matrix,max_size*max_size*max_size,vector,&solution,accuracy);
		break;
	case CG:
		result=cg_solve_eq(coeff_matrix,max_size*max_size*max_size,vector,&solution,accuracy);
		break;
	case SSOR_PCG:
		result=ssor_pcg_solve_eq(coeff_matrix,max_size*max_size*max_size,vector,&solution,accuracy);
		break;
	}
	free(vector);
	destroy_sparse_matrix(coeff_matrix,max_size*max_size*max_size);
	switch(result)
	{
	case COEFF_ERR:
		fclose(output_file);
		printf("Error: An unexpected error happened. This means noting but there's a bug in this program.\n");
		return -3;
	case NOT_CONVERGE:
		fclose(output_file);
		printf("Error: The iteration doesn't converge.\n");
		return -3;
	}
	printf("Poisson eq solved.\n");
	printsolu(output_file,solution,max_size);
	fclose(output_file);
	return 0;
}

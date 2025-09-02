#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include "svdpi.h"

#pragma warning(disable:4996)

typedef struct{
    char                M, N; // magic number
    int                 width;
    int                 height;
    int                 max;
    unsigned    int    **pixels; 
} Image;

typedef struct{
    unsigned int **filter;
} Filter;


enum{FALSE, TRUE};


int fnRead(char*fileNm, Image* img)
{
    FILE* fp;

    if(fileNm == NULL){
        fprintf(stderr, "fnReadPPM ERROR\n");
        return FALSE;
    }

    fp = fopen(fileNm, "rb");
    if(fileNm == NULL){
        fprintf(stderr, "Cannot Open File : %s\n", fileNm);
        return FALSE;
    }

    fscanf(fp, "%c%c\n", &img->M, &img->N); // Read Magic Number
    fscanf(fp, "%d %d\n", &img->height, &img->width); // Read size
    fscanf(fp, "%d\n", &img->max); // Read Max
    //printf("##Read File Info##\n");
    //printf("TYPE   : %c%c      #\nHEIGHT : %d     #\nWIDTH  : %d     #\nMAX    : %d     #\n", img->M,img->N,img->height,img->width,img->max);
    //printf("##################\n");

    if(img->M != 'P' || img->N != '2'){
        fprintf(stderr, "Not correct Image Format.\n");
        return FALSE;
    }

    // Memory
	img->pixels = (unsigned int**)calloc((img->height), sizeof(unsigned int*));
    
	for(int i=0; i<(img->height); i++){
		img->pixels[i] = (unsigned int*)calloc(img->width, sizeof(unsigned int));
	}

    //read file
    for(int i=0; i<(img->height); i++){
        for(int j=0;j<(img->width);j++){
            fscanf(fp, "%d\n", &img->pixels[i][j]);
        }
    }

    fclose(fp);

    return TRUE;
}


void fnClose(Image* img)
{
    for(int i=0; i<(img->height); i++){
        free(img->pixels[i]);
    }
    free(img->pixels);
}


int fnWrite(char*fileNm, Image* img)
{
    FILE* fp;

    fp = fopen(fileNm, "w");
    if(fp == NULL){
        fprintf(stderr, "Fail to Create File.\n");
        return FALSE;
    }

    //fprintf(fp, "%c%c\n", 'P', '2');
    fprintf(fp, "%c%c\n", img->M, img->N);
    fprintf(fp, "%d %d\n", img->height, img->width);
    fprintf(fp, "%d\n", img->max);

 	for(int i=0; i<img->height; i++){
		for(int j=0; j<img->width; j++){			
			fprintf(fp, "%3d ", img->pixels[i][j]);
		}
        fprintf(fp,"\n");
	}  

    fclose(fp);

    return TRUE;
}


int fnBlur(Image* img_org, Image* img_blur, Filter* filter, Filter* filter_in, int weight_wr_mode, int blur_mode, int mirror_mode, int w1, int w2, int w3, int w4, int w5, int w6, int w7, int w8, int w9)
{    
    // Header Value
    img_blur->M      = img_org->M;
    img_blur->N      = img_org->N;
    img_blur->height = img_org->height;
    img_blur->width  = img_org->width;
    img_blur->max    = img_org->max;

    int data_blur    = 0 ;
  	int x 		     = 0 ;
  	int weight_total = 0 ;

    // Mamory Allocation
    img_blur->pixels = (unsigned int**)calloc(img_blur->height, sizeof(unsigned int*));

    for(int i=0; i<img_blur->height; i++){
        img_blur->pixels[i] = (unsigned int*)calloc(img_blur->width, sizeof(unsigned int));
    }

    filter->filter = (unsigned int**)calloc(3, sizeof(unsigned int));

    for(int i=0; i<3; i++){
        filter->filter[i] = (unsigned int*)calloc(3, sizeof(unsigned int)); 
    }

    filter_in->filter = (unsigned int**)calloc(3, sizeof(unsigned int));

    for(int i=0; i<3; i++){
        filter_in->filter[i] = (unsigned int*)calloc(3, sizeof(unsigned int)); 
    }
    
  	//Setting Filter Value  
  	filter_in->filter[0][0] = w1 ; 
  	filter_in->filter[0][1] = w2 ; 
  	filter_in->filter[0][2] = w3 ; 
  	filter_in->filter[1][0] = w4 ; 
  	filter_in->filter[1][1] = w5 ; 
  	filter_in->filter[1][2] = w6 ; 
  	filter_in->filter[2][0] = w7 ; 
  	filter_in->filter[2][1] = w8 ; 
  	filter_in->filter[2][2] = w9 ; 

  
  	if(weight_wr_mode){
    	for(int i=0; i<3; i++){
        	for(int j=0; j<3; j++){
              filter->filter[i][j] = filter_in->filter[i][j];
              weight_total = weight_total + filter_in->filter[i][j];
            }
        }
  	}
  	else {
    	for(int i=0; i<3; i++){
        	for(int j=0; j<3; j++){
            	if(i==1){
                	if(j==1){
                    	filter->filter[i][j] = 4;
                	}
                	else{
                    	filter->filter[i][j] = 2;
                	}
            	}
            	else{
                	if(j==1){
                    	filter->filter[i][j] = 2;
                	}
                	else{
                    	filter->filter[i][j] = 1;
                	}
            	}
        	}
    	}
  	}

    // Function
    for(int i=0; i<img_blur->height; i++){
        for(int j=0; j<img_blur->width; j++){
          	x = (!mirror_mode) ? j : ((img_blur->width)-1) - j;
            if(i==0){
                if(j==0){
                    data_blur = filter->filter[0][0]*img_org->pixels[i+1][j+1]  + filter->filter[0][1]*img_org->pixels[i+1][j] + filter->filter[0][2]*img_org->pixels[i+1][j+1] +
                                filter->filter[1][0]*img_org->pixels[i][j+1]    + filter->filter[1][1]*img_org->pixels[i][j]   + filter->filter[1][2]*img_org->pixels[i][j+1]   +
                                filter->filter[2][0]*img_org->pixels[i+1][j+1]  + filter->filter[2][1]*img_org->pixels[i+1][j] + filter->filter[2][2]*img_org->pixels[i+1][j+1];

                    img_blur->pixels[i][x] = (weight_wr_mode) ? data_blur/weight_total :
                      						 (!blur_mode    ) ?	img_org->pixels[i][j]  : data_blur/(16);

                    //printf("0=%d\n",j);
                    data_blur = 0;
                }
                else if(j<img_blur->width-1){
                    data_blur = filter->filter[0][0]*img_org->pixels[i+1][j-1] + filter->filter[0][1]*img_org->pixels[i+1][j] + filter->filter[0][2]*img_org->pixels[i+1][j+1] +
                                filter->filter[1][0]*img_org->pixels[i][j-1]   + filter->filter[1][1]*img_org->pixels[i][j]   + filter->filter[1][2]*img_org->pixels[i][j+1]   +
                                filter->filter[2][0]*img_org->pixels[i+1][j-1] + filter->filter[2][1]*img_org->pixels[i+1][j] + filter->filter[2][2]*img_org->pixels[i+1][j+1];

                    img_blur->pixels[i][x] = (weight_wr_mode) ? data_blur/weight_total :
                      						 (!blur_mode    ) ?	img_org->pixels[i][j]  : data_blur/(16);
                    //printf("0<%d<511\n",j);
                    
                    data_blur = 0;
                }
                else if(j==img_blur->width-1){
                    data_blur = filter->filter[0][0]*img_org->pixels[i+1][j-1] + filter->filter[0][1]*img_org->pixels[i+1][j] + filter->filter[0][2]*img_org->pixels[i+1][j-1] +
                                filter->filter[1][0]*img_org->pixels[i][j-1]   + filter->filter[1][1]*img_org->pixels[i][j]   + filter->filter[1][2]*img_org->pixels[i][j-1]   +
                                filter->filter[2][0]*img_org->pixels[i+1][j-1] + filter->filter[2][1]*img_org->pixels[i+1][j] + filter->filter[2][2]*img_org->pixels[i+1][j-1];

                    img_blur->pixels[i][x] = (weight_wr_mode) ? data_blur/weight_total :
                      						 (!blur_mode    ) ?	img_org->pixels[i][j]  : data_blur/(16);
                    //printf("%d = 511\n",j);

                    data_blur = 0;
                }
            }
            
            else if(i<img_blur->height-1){
                if(j==0){
                    data_blur = filter->filter[0][0]*img_org->pixels[i-1][j+1] + filter->filter[0][1]*img_org->pixels[i-1][j] + filter->filter[0][2]*img_org->pixels[i-1][j+1] +
                                filter->filter[1][0]*img_org->pixels[i][j+1]   + filter->filter[1][1]*img_org->pixels[i][j]   + filter->filter[1][2]*img_org->pixels[i][j+1]   +
                                filter->filter[2][0]*img_org->pixels[i+1][j+1] + filter->filter[2][1]*img_org->pixels[i+1][j] + filter->filter[2][2]*img_org->pixels[i+1][j+1];

                    img_blur->pixels[i][x] = (weight_wr_mode) ? data_blur/weight_total :
                      						 (!blur_mode    ) ?	img_org->pixels[i][j]  : data_blur/(16);
                    //printf("0=%d\n",j);

                    data_blur = 0;
                }
                else if(j<img_blur->width-1){
                    data_blur = filter->filter[0][0]*img_org->pixels[i-1][j-1] + filter->filter[0][1]*img_org->pixels[i-1][j] + filter->filter[0][2]*img_org->pixels[i-1][j+1] +
                                filter->filter[1][0]*img_org->pixels[i][j-1]   + filter->filter[1][1]*img_org->pixels[i][j]   + filter->filter[1][2]*img_org->pixels[i][j+1]   +
                                filter->filter[2][0]*img_org->pixels[i+1][j-1] + filter->filter[2][1]*img_org->pixels[i+1][j] + filter->filter[2][2]*img_org->pixels[i+1][j+1];

                    img_blur->pixels[i][x] = (weight_wr_mode) ? data_blur/weight_total :
                      						 (!blur_mode    ) ?	img_org->pixels[i][j]  : data_blur/(16);
                    //printf("0<%d<511\n",j);

                    data_blur = 0;
                }
                else if(j==img_blur->width-1){
                    data_blur = filter->filter[0][0]*img_org->pixels[i-1][j-1] + filter->filter[0][1]*img_org->pixels[i-1][j] + filter->filter[0][2]*img_org->pixels[i-1][j-1] +
                                filter->filter[1][0]*img_org->pixels[i][j-1]   + filter->filter[1][1]*img_org->pixels[i][j]   + filter->filter[1][2]*img_org->pixels[i][j-1]   +
                                filter->filter[2][0]*img_org->pixels[i+1][j-1] + filter->filter[2][1]*img_org->pixels[i+1][j] + filter->filter[2][2]*img_org->pixels[i+1][j-1];

                    img_blur->pixels[i][x] = (weight_wr_mode) ? data_blur/weight_total :
                      						 (!blur_mode    ) ?	img_org->pixels[i][j]  : data_blur/(16);
                    //printf("i=%d / %d=511\n", i, j);

                    data_blur = 0;    
                }
                //printf("%d ok\n",i);
            }
            else if(i==img_blur->height-1){
                //printf("ok2 i=%d j=%d\n", i, j);
                if(j==0){
                //printf("ok3 i=%d j=%d\n", i, j);
                    data_blur = filter->filter[0][0]*img_org->pixels[i-1][j+1] + filter->filter[0][1]*img_org->pixels[i-1][j] + filter->filter[0][2]*img_org->pixels[i-1][j+1] +
                                filter->filter[1][0]*img_org->pixels[i][j+1]   + filter->filter[1][1]*img_org->pixels[i][j]   + filter->filter[1][2]*img_org->pixels[i][j+1]   +
                                filter->filter[2][0]*img_org->pixels[i-1][j+1] + filter->filter[2][1]*img_org->pixels[i-1][j] + filter->filter[2][2]*img_org->pixels[i-1][j+1];

                    img_blur->pixels[i][x] = (weight_wr_mode) ? data_blur/weight_total :
                      						 (!blur_mode    ) ?	img_org->pixels[i][j]  : data_blur/(16);

                    data_blur = 0;
                }
                else if(j<img_blur->width-1){
                //printf("aaa4 i=%d j=%d\n", i, j);
                    data_blur = filter->filter[0][0]*img_org->pixels[i-1][j-1] + filter->filter[0][1]*img_org->pixels[i-1][j] + filter->filter[0][2]*img_org->pixels[i-1][j+1] +
                                filter->filter[1][0]*img_org->pixels[i][j-1]   + filter->filter[1][1]*img_org->pixels[i][j]   + filter->filter[1][2]*img_org->pixels[i][j+1]   +
                                filter->filter[2][0]*img_org->pixels[i-1][j-1] + filter->filter[2][1]*img_org->pixels[i-1][j] + filter->filter[2][2]*img_org->pixels[i-1][j+1];

                    img_blur->pixels[i][x] = (weight_wr_mode) ? data_blur/weight_total :
                      						 (!blur_mode    ) ?	img_org->pixels[i][j]  : data_blur/(16);

                    data_blur = 0;
                }
                else if(j==img_blur->width-1){
                //printf("aaa5 i=%d j=%d\n", i, j);
                    data_blur = filter->filter[0][0]*img_org->pixels[i-1][j-1] + filter->filter[0][1]*img_org->pixels[i-1][j] + filter->filter[0][2]*img_org->pixels[i-1][j-1] +
                                filter->filter[1][0]*img_org->pixels[i][j-1]   + filter->filter[1][1]*img_org->pixels[i][j]   + filter->filter[1][2]*img_org->pixels[i][j-1]   +
                                filter->filter[2][0]*img_org->pixels[i-1][j-1] + filter->filter[2][1]*img_org->pixels[i-1][j] + filter->filter[2][2]*img_org->pixels[i-1][j-1];

                    img_blur->pixels[i][x] = (weight_wr_mode) ? data_blur/weight_total :
                      						 (!blur_mode    ) ?	img_org->pixels[i][j]  : data_blur/(16);

                    data_blur = 0;                    
                }
            }
        }       
    }

        //printf("aaa1\n");
    return TRUE;
}
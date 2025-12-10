rm(list=ls())

library(acepack)
library(arm)
library(backports)
library(base64enc)
library(bitops)
library(boot)
library(car)
library(caTools)
library(checkmate)
library(chron)
library(colorspace)
library(compareGroups)
library(data.table)
library(DescTools)
library(dichromat)
library(digest)
library(dplyr)
library(evaluate)
library(foreign)
library(Formula)
library(gam)
library(ggplot2)
library(gplots)
library(gratia)
library(gridExtra)
library(gtable)
library(haven)
library(highr)
library(Hmisc)
library(htmlTable)
library(htmltools)
library(htmlwidgets)
library(icenReg)
library(irr)
library(jsonlite)
library(knitr)
library(labeling)
library(latticeExtra)
library(lazyeval)
library(lme4)
library(lmerTest)
library(lmtest)
library(MASS)
library(magrittr)
library(markdown)
library(MatrixModels)
library(meta)
library(metafor)
library(mgcv)
library(missRanger)
library(mime)
library(minqa)
library(MuMIn)
library(munsell)
library(nephro)
library(nlme)
library(pbkrtest)
library(plotrix)
library(plyr)
library(psy)
library(purrr)
library(quantreg)
library(RColorBrewer)
library(Rcpp)
library(RcppEigen)
library(rlang)
library(ROCR)
library(RODBC)
library(reshape2)
library(sandwich)
library(scales)
library(smoothHR)
library(SparseM)
library(standardize)
library(stringi)
library(stringr)
library(survival)
library(tibble)
library(tidyr)
library(vcd)
library(viridis)
library(viridisLite)
library(yaml)


RutinesLocals<- "D:/R/Rutinas"
source(file.path(RutinesLocals,"carrega.llibreria.r"))
source(file.path(RutinesLocals,"merge2.r"))
source(file.path(RutinesLocals,"fix2.r"))
source(file.path(RutinesLocals,"table2.r"))
source(file.path(RutinesLocals,"subset2.r"))
source(file.path(RutinesLocals,"format2.r"))
source(file.path(RutinesLocals,"order2.r"))
source(file.path(RutinesLocals,"intervals.r"))


### GUAPAS ###
##############

guapa<-function(x)
{
  redondeo<-ifelse(abs(x)<0.00001,signif(x,1),
                   ifelse(abs(x)<0.0001,signif(x,1),
                          ifelse(abs(x)<0.001,signif(x,1),
                                 ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                        ifelse(abs(x)<1,sprintf("%.2f",round(x,2)),
                                               ifelse(abs(x)<10,sprintf("%.2f",round(x,2)),
                                                      ifelse(abs(x)<100,sprintf("%.1f",round(x,1)),
                                                             ifelse(abs(x)>=100,round(x,0),round(x,0)))))))))
  return(redondeo)
}

ic_guapa<-function(x,y,z)
{
  ic<-paste(x," [",y,"; ",z,"]",sep="")
  return(ic)
}

ic_guapa2<-function(x,y,z)
{
  ic<-paste(x," (",y," to ",z,")",sep="")
  return(ic)
}

pval_guapa<-function(x)
{
  pval<-ifelse(x<0.00001,"<0.00001",
               ifelse(x<0.001,"<0.001",
                      ifelse(abs(x)<0.01,sprintf("%.3f",round(x,3)),
                             ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                    ifelse(abs(x)<1,sprintf("%.3f",round(x,3)),guapa(x))))))
  return(pval)
}

pval_guapa2<-function(x)
{
  pval<-ifelse(x<0.00001," < 0.00001",
               ifelse(x<0.001," < 0.001",
                      ifelse(abs(x)<0.01,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                             ifelse(abs(x)<0.1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                                    ifelse(abs(x)<1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),guapa(x))))))
  return(pval)
}

mean_ic_guapa <- function(x, na.rm=FALSE) 
{
  if (na.rm) x <- na.omit(x)
  se<-sqrt(var(x)/length(x))
  z<-qnorm(1-0.05/2)
  media<-mean(x)
  ic95a<-guapa(media-(z*se))
  ic95b<-guapa(media+(z*se))
  media<-guapa(media)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

mean_sd_guapa <- function(x) 
{
  media<-guapa(mean(x, na.rm=TRUE))
  sd<-guapa(sd(x, na.rm=TRUE))
  end<-paste(media," (",sd,")",sep="")
  return(end)
}

beta_se_ic_guapa <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

beta_se_ic_guapa2 <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa2(media,ic95a,ic95b)
  return(ic_ok)
}

beta_se_ic_guapa3 <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-(x-(z*y))
  ic95b<-(x+(z*y))
  media<-(x)
  ic_ok<-c(media,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa2 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa3 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-round(exp(x),3)
  ic95a<-round(exp(x-(z*y)),3)
  ic95b<-round(exp(x+(z*y)),3)
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

header.true <- function(df)
{
  names(df) <- as.character(unlist(df[1,]))
  df[-1,]
}

z<-qnorm(1-0.05/2)
se <- function(x) sqrt(var(x) / length(x))

closest<-function(xv,sv){
  xv[which(abs(xv-sv)==min(abs(xv-sv)))] }

# Suppress scientific notation for coefficients (no "4e-04", instead "0.0004")
options(scipen=999)

dir.create("D:/Artículos/Viviana Sandoval - RIO")
dir.create("D:/Artículos/Viviana Sandoval - RIO/Data")
dir.create("D:/Artículos/Viviana Sandoval - RIO/Outputs")

setwd("D:/Artículos/Viviana Sandoval - RIO")


### CALCULO TRIGLICERIDOS POSTPRANDIALES ###
############################################

datos<-read.csv2("./Data/tg_auc.csv",header=TRUE,sep=";",dec=".")

tg_postpr <- datos %>%
  group_by(id, visita) %>%
  arrange(hora, .by_group = TRUE) %>%
  summarise(
    {
      df <- data.frame(hora = hora, tg = tg)
      df <- df[is.finite(df$hora) & is.finite(df$tg), ]
      df <- df[!is.na(df$hora) & !is.na(df$tg), ]
      n_tiempos <- dplyr::n_distinct(df$hora)
      if (n_tiempos < 3 || !any(df$hora == 0)) {
        tibble(
          iAUC = NA_real_,
          Tmax = NA_real_,
          Cmax = NA_real_
        )
      } else {
        tg_baseline <- df$tg[df$hora == 0][1]
        f <- splinefun(x = df$hora, y = df$tg, method = "natural")
        grid_t <- seq(min(df$hora), max(df$hora), by = 0.01)
        tg_smooth <- f(grid_t)
        idx_max <- which.max(tg_smooth)
        Tmax <- grid_t[idx_max]
        Cmax <- tg_smooth[idx_max]
        tg_inc <- tg_smooth - tg_baseline
        tg_inc[tg_inc < 0] <- 0
        iAUC_val <- DescTools::AUC(x = grid_t, y = tg_inc, method = "trapezoid")
        
        tibble(
          iAUC = iAUC_val/60,
          Tmax = Tmax,
          Cmax = Cmax
        )
      }
    },
    .groups = "drop"
  )

tg_postpr <- tg_postpr %>%
  rename(
    tg_iAUC = iAUC,
    tg_tmax = Tmax,
    tg_cmax = Cmax
  ) %>%
  pivot_wider(
    id_cols   = id,
    names_from  = visita,
    values_from = c(tg_iAUC, tg_tmax, tg_cmax),
    names_glue = "{.value}_v{visita}"
  )

write.table(as.data.frame(tg_postpr),"./Data/tg_postpr.csv",sep=";",col.names=TRUE,row.names=FALSE)
# Unidades de las medidas resultantes: tg_iAUC en mg/dL·h, tg_tmax en minutos, tg_cmax en mg/dL


### CALCULO PENDIENTES METABOLISMO GLUCOS 2H ###
################################################

datos <- read.csv2("./Data/gluc_pendientes.csv",header=TRUE,sep=";",dec=".")

dif2h <- datos %>%
  group_by(id, visita) %>%
  summarise(
    {
      df <- data.frame(hora, glucosa, insulina, homa)
      df <- df[is.finite(df$hora) & !is.na(df$hora), ]
      if (nrow(df) < 2) {
        return(tibble(
          glucosa_dif2h  = NA_real_,
          insulina_dif2h = NA_real_,
          homa_dif2h     = NA_real_
        ))
      }
      idx0 <- which.min(df$hora)
      t0   <- df$hora[idx0]
      g0   <- df$glucosa[idx0]
      i0   <- df$insulina[idx0]
      h0   <- df$homa[idx0]
      dif_t <- abs(df$hora - 120)
      dif_t[idx0] <- Inf  # aseguramos que no elige el basal
      
      if (all(is.infinite(dif_t))) {
        return(tibble(
          glucosa_dif2h  = NA_real_,
          insulina_dif2h = NA_real_,
          homa_dif2h     = NA_real_
        ))
      }
      
      idx2 <- which.min(dif_t)
      t2   <- df$hora[idx2]
      g2   <- df$glucosa[idx2]
      i2   <- df$insulina[idx2]
      h2   <- df$homa[idx2]
      
      dt_h <- (t2 - t0) / 60
      if (is.na(dt_h) || dt_h <= 0) {
        tibble(
          glucosa_dif2h  = NA_real_,
          insulina_dif2h = NA_real_,
          homa_dif2h     = NA_real_
        )
      } else {
        tibble(
          glucosa_dif2h  = (g2 - g0) / dt_h,
          insulina_dif2h = (i2 - i0) / dt_h,
          homa_dif2h     = (h2 - h0) / dt_h
        )
      }
    },
    .groups = "drop"
  )

dif2h <- dif2h %>%
  pivot_wider(
    id_cols = id,
    names_from = visita,
    values_from = c(glucosa_dif2h, insulina_dif2h, homa_dif2h),
    names_glue = "{.value}_v{visita}"
  )

write.table(as.data.frame(dif2h),"./Data/gluc_dif2h.csv",sep=";",col.names=TRUE,row.names=FALSE)
# Unidades: glucosa_dif2h: mg/dl·h; insulina_dif2h: uUI/ml·h; HOMA: HOMA-IR units/h


### SCORE DE CALIDAD DIETETICA GENERAL ###
##########################################

comidas<-read.csv2("./Data/v1_comidas.csv",header=TRUE,sep=";",dec=".")
comidas <- comidas %>%
  mutate(
    # Componentes "positivos"
    desayuno_sc = desayuno,
    ayuno_sc    = ayuno_horas / max(comidas$ayuno_horas, na.rm = TRUE), # normalizamos 0–1
    # Componentes "negativos" (invertidos)
    recena_sc     = 1 - recena,                      
    colaciones_sc = 1 - (colaciones / max(comidas$colaciones, na.rm = TRUE)),
    bebidas_sc    = 1 - bebidas,
    # Forzamos a 0–1 por si hubiera valores > max o negativos
    colaciones_sc = pmax(pmin(colaciones_sc, 1), 0),
    bebidas_sc    = pmax(pmin(bebidas_sc,    1), 0),
    ayuno_sc      = pmax(pmin(ayuno_sc,      1), 0),
    # Índice global (0–1 aprox.; más alto = mejor calidad)
    dietaq = rowMeans(
      cbind(desayuno_sc, recena_sc, colaciones_sc, bebidas_sc, ayuno_sc),
      na.rm = TRUE
    )
  )
comidas<-comidas[,c("id","dietaq")]


### CREACION DE BASE DE DATOS DEFINITIVA ###
############################################

# FUSIONES #

v1_crf<-read.csv2("./Data/v1_crf.csv",header=TRUE,sep=";",dec=".")
v1_bq<-read.csv2("./Data/v1_bq.csv",header=TRUE,sep=";",dec=".")
v1_bia<-read.csv2("./Data/v1_bia.csv",header=TRUE,sep=";",dec=".")
v1_tg<-tg_postpr[,c("id","tg_iAUC_v1","tg_tmax_v1","tg_cmax_v1")]
names(v1_tg)<-c("id","tg_iAUC","tg_tmax","tg_cmax")
v1_gluc<-dif2h[,c("id","glucosa_dif2h_v1","insulina_dif2h_v1","homa_dif2h_v1")]
names(v1_gluc)<-c("id","glucosa_dif2h","insulina_dif2h","homa_dif2h")
v1<-merge2(v1_crf,v1_bq,by.id=c("id"),all.x=TRUE,sort=FALSE)
v1<-merge2(v1,v1_bia,by.id=c("id"),all.x=TRUE,sort=FALSE)
v1<-merge2(v1,v1_tg,by.id=c("id"),all.x=TRUE,sort=FALSE)
v1<-merge2(v1,v1_gluc,by.id=c("id"),all.x=TRUE,sort=FALSE)
v1$imc<-v1$peso/((v1$altura/100)^2)
v1$whr<-v1$cintura/v1$cadera
v1$obes<-with(v1,ifelse(imc<25,1,
                        ifelse(imc<30,2,
                               ifelse(imc>=30,3,NA))))
v1$obabd<-with(v1,ifelse(cintura>88 & mujer==1,1,
                         ifelse(cintura<=88 & mujer==1,0,
                                ifelse(cintura>102 & mujer==0,1,
                                       ifelse(cintura<=102 & mujer==0,0,NA)))))
v1$aip<-log(v1$tg/v1$hdlc)
v1$mvltpa<-v1$met_moderada+v1$met_vigorosa
v1<-v1[,c("id","mujer","edad","grupo","inmunosup","hipolip_antiinf","suplementos","activo_fisicamente_ayer","alcohol_ayer","enfermo_mes",
          "ayuno_horas","obes","obabd","mvltpa","sedentarismo_horas",
          "pas","pad","pulso","imc","cintura","cadera","whr",
          "tc","tg","hdlc","ldlc","vldlc","nonhdlc","aip","glucosa","insulina","homa",
          "std_wt","lbm","tbw","ecw","icw","mbf","pbf","ratio","bmr","lt_arm","rt_arm","lt_leg","rt_leg","trunk","impedance",
          "tg_iAUC","tg_tmax","tg_cmax","glucosa_dif2h","insulina_dif2h","homa_dif2h")]
v1$ecw<-with(v1,ifelse(ecw>40,NA,ecw))
v1$ratio<-with(v1,ifelse(ratio>0.6,NA,ratio))

v2_crf<-read.csv2("./Data/v2_crf.csv",header=TRUE,sep=";",dec=".")
v2_bq<-read.csv2("./Data/v2_bq.csv",header=TRUE,sep=";",dec=".")
v2_bia<-read.csv2("./Data/v2_bia.csv",header=TRUE,sep=";",dec=".")
v2_tg<-tg_postpr[,c("id","tg_iAUC_v2","tg_tmax_v2","tg_cmax_v2")]
names(v2_tg)<-c("id","tg_iAUC","tg_tmax","tg_cmax")
v2_gluc<-dif2h[,c("id","glucosa_dif2h_v2","insulina_dif2h_v2","homa_dif2h_v2")]
names(v2_gluc)<-c("id","glucosa_dif2h","insulina_dif2h","homa_dif2h")
v2<-merge2(v2_crf,v2_bq,by.id=c("id"),all.x=TRUE,sort=FALSE)
v2<-merge2(v2,v2_bia,by.id=c("id"),all.x=TRUE,sort=FALSE)
v2<-merge2(v2,v2_tg,by.id=c("id"),all.x=TRUE,sort=FALSE)
v2<-merge2(v2,v2_gluc,by.id=c("id"),all.x=TRUE,sort=FALSE)
v2$imc<-v2$peso/((v2$altura/100)^2)
v2$whr<-v2$cintura/v2$cadera
v2$obes<-with(v2,ifelse(imc<25,1,
                        ifelse(imc<30,2,
                               ifelse(imc>=30,3,NA))))
v2$obabd<-with(v2,ifelse(cintura>88 & mujer==1,1,
                         ifelse(cintura<=88 & mujer==1,0,
                                ifelse(cintura>102 & mujer==0,1,
                                       ifelse(cintura<=102 & mujer==0,0,NA)))))
v2$aip<-log(v2$tg/v2$hdlc)
v2$mvltpa<-v2$met_moderada+v2$met_vigorosa
v2<-v2[,c("id","inmunosup","hipolip_antiinf","suplementos","activo_fisicamente_ayer","alcohol_ayer","enfermo_mes",
          "ayuno_horas","obes","obabd","mvltpa","sedentarismo_horas",
          "pas","pad","pulso","imc","cintura","cadera","whr",
          "tc","tg","hdlc","ldlc","vldlc","nonhdlc","aip","glucosa","insulina","homa",
          "std_wt","lbm","tbw","ecw","icw","mbf","pbf","ratio","bmr","lt_arm","rt_arm","lt_leg","rt_leg","trunk","impedance",
          "tg_iAUC","tg_tmax","tg_cmax","glucosa_dif2h","insulina_dif2h","homa_dif2h")]
v2$ecw<-with(v2,ifelse(ecw>40,NA,ecw))
v2$ratio<-with(v2,ifelse(ratio>0.6,NA,ratio))

v3_crf<-read.csv2("./Data/v3_crf.csv",header=TRUE,sep=";",dec=".")
v3_bq<-read.csv2("./Data/v3_bq.csv",header=TRUE,sep=";",dec=".")
v3_bia<-read.csv2("./Data/v3_bia.csv",header=TRUE,sep=";",dec=".")
v3_tg<-tg_postpr[,c("id","tg_iAUC_v3","tg_tmax_v3","tg_cmax_v3")]
names(v3_tg)<-c("id","tg_iAUC","tg_tmax","tg_cmax")
v3_gluc<-dif2h[,c("id","glucosa_dif2h_v3","insulina_dif2h_v3","homa_dif2h_v3")]
names(v3_gluc)<-c("id","glucosa_dif2h","insulina_dif2h","homa_dif2h")
v3<-merge2(v3_crf,v3_bq,by.id=c("id"),all.x=TRUE,sort=FALSE)
v3<-merge2(v3,v3_bia,by.id=c("id"),all.x=TRUE,sort=FALSE)
v3<-merge2(v3,v3_tg,by.id=c("id"),all.x=TRUE,sort=FALSE)
v3<-merge2(v3,v3_gluc,by.id=c("id"),all.x=TRUE,sort=FALSE)
v3$imc<-v3$peso/((v3$altura/100)^2)
v3$whr<-v3$cintura/v3$cadera
v3$obes<-with(v3,ifelse(imc<25,1,
                        ifelse(imc<30,2,
                               ifelse(imc>=30,3,NA))))
v3$obabd<-with(v3,ifelse(cintura>88 & mujer==1,1,
                         ifelse(cintura<=88 & mujer==1,0,
                                ifelse(cintura>102 & mujer==0,1,
                                       ifelse(cintura<=102 & mujer==0,0,NA)))))
v3$aip<-log(v3$tg/v3$hdlc)
v3$mvltpa<-v3$met_moderada+v3$met_vigorosa
v3<-v3[,c("id","inmunosup","hipolip_antiinf","suplementos","activo_fisicamente_ayer","alcohol_ayer","enfermo_mes",
          "ayuno_horas","obes","obabd","mvltpa","sedentarismo_horas",
          "pas","pad","pulso","imc","cintura","cadera","whr",
          "tc","tg","hdlc","ldlc","vldlc","nonhdlc","aip","glucosa","insulina","homa",
          "std_wt","lbm","tbw","ecw","icw","mbf","pbf","ratio","bmr","lt_arm","rt_arm","lt_leg","rt_leg","trunk","impedance",
          "tg_iAUC","tg_tmax","tg_cmax","glucosa_dif2h","insulina_dif2h","homa_dif2h")]
v3$ecw<-with(v3,ifelse(ecw>40,NA,ecw))
v3$ratio<-with(v3,ifelse(ratio>0.6,NA,ratio))

v4_crf<-read.csv2("./Data/v4_crf.csv",header=TRUE,sep=";",dec=".")
v4_bq<-read.csv2("./Data/v4_bq.csv",header=TRUE,sep=";",dec=".")
v4_bia<-read.csv2("./Data/v4_bia.csv",header=TRUE,sep=";",dec=".")
v4_tg<-tg_postpr[,c("id","tg_iAUC_v4","tg_tmax_v4","tg_cmax_v4")]
names(v4_tg)<-c("id","tg_iAUC","tg_tmax","tg_cmax")
v4_gluc<-dif2h[,c("id","glucosa_dif2h_v4","insulina_dif2h_v4","homa_dif2h_v4")]
names(v4_gluc)<-c("id","glucosa_dif2h","insulina_dif2h","homa_dif2h")
v4<-merge2(v4_crf,v4_bq,by.id=c("id"),all.x=TRUE,sort=FALSE)
v4<-merge2(v4,v4_bia,by.id=c("id"),all.x=TRUE,sort=FALSE)
v4<-merge2(v4,v4_tg,by.id=c("id"),all.x=TRUE,sort=FALSE)
v4<-merge2(v4,v4_gluc,by.id=c("id"),all.x=TRUE,sort=FALSE)
v4$imc<-v4$peso/((v4$altura/100)^2)
v4$whr<-v4$cintura/v4$cadera
v4$obes<-with(v4,ifelse(imc<25,1,
                        ifelse(imc<30,2,
                               ifelse(imc>=30,3,NA))))
v4$obabd<-with(v4,ifelse(cintura>88 & mujer==1,1,
                         ifelse(cintura<=88 & mujer==1,0,
                                ifelse(cintura>102 & mujer==0,1,
                                       ifelse(cintura<=102 & mujer==0,0,NA)))))
v4$aip<-log(v4$tg/v4$hdlc)
v4$mvltpa<-v4$met_moderada+v4$met_vigorosa
v4<-v4[,c("id","fumador","inmunosup","hipolip_antiinf","suplementos","activo_fisicamente_ayer","alcohol_ayer","enfermo_mes",
          "ayuno_horas","obes","obabd","mvltpa","sedentarismo_horas",
          "pas","pad","pulso","imc","cintura","cadera","whr",
          "tc","tg","hdlc","ldlc","vldlc","nonhdlc","aip","glucosa","insulina","homa",
          "std_wt","lbm","tbw","ecw","icw","mbf","pbf","ratio","bmr","lt_arm","rt_arm","lt_leg","rt_leg","trunk","impedance",
          "tg_iAUC","tg_tmax","tg_cmax","glucosa_dif2h","insulina_dif2h","homa_dif2h")]
v4$ecw<-with(v4,ifelse(ecw>40,NA,ecw))
v4$ratio<-with(v4,ifelse(ratio>0.6,NA,ratio))


# ANALISIS DE NORMALIDAD #

norm_vars<-c("id","mvltpa","sedentarismo_horas","pas","pad","pulso","imc","cintura","cadera","whr",
             "tc","tg","hdlc","ldlc","vldlc","nonhdlc","aip","glucosa","insulina","homa",
             "std_wt","lbm","tbw","ecw","icw","mbf","pbf","ratio","bmr","lt_arm","rt_arm","lt_leg","rt_leg","trunk","impedance",
             "tg_iAUC","tg_tmax","tg_cmax","glucosa_dif2h","insulina_dif2h","homa_dif2h")
norm<-rbind(v1[,norm_vars],v2[,norm_vars],v3[,norm_vars],v4[,norm_vars])

#plot(compareGroups(~homa_dif2h,data=norm))
# No-normales: mvltpa, 


# FUSIONES FINALES #

names(v1)[-c(1:4)]<-paste(names(v1)[-c(1:4)],"_v1",sep="")
names(v2)[-c(1)]<-paste(names(v2)[-c(1)],"_v2",sep="")
names(v3)[-c(1)]<-paste(names(v3)[-c(1)],"_v3",sep="")
names(v4)[-c(1:2)]<-paste(names(v4)[-c(1:2)],"_v4",sep="")
dat<-merge2(v1,v2,by.id=c("id"),all.x=TRUE,sort=FALSE)
dat<-merge2(dat,v3,by.id=c("id"),all.x=TRUE,sort=FALSE)
dat<-merge2(dat,v4,by.id=c("id"),all.x=TRUE,sort=FALSE)
dat<-merge2(dat,comidas,by.id=c("id"),all.x=TRUE,sort=FALSE)

dat$inmunosup<-ifelse(rowSums(dat[,c("inmunosup_v1","inmunosup_v2","inmunosup_v3","inmunosup_v4")]==1, na.rm=TRUE)>0,1,0)
dat$hipolip_antiinf<-ifelse(rowSums(dat[,c("hipolip_antiinf_v1","hipolip_antiinf_v2","hipolip_antiinf_v3","hipolip_antiinf_v4")]==1, na.rm=TRUE)>0,1,0)
dat$suplementos<-ifelse(rowSums(dat[,c("suplementos_v1","suplementos_v2","suplementos_v3","suplementos_v4")]==1, na.rm=TRUE)>0,1,0)
dat$actfis_ayer<-ifelse(rowSums(dat[,c("activo_fisicamente_ayer_v1","activo_fisicamente_ayer_v2","activo_fisicamente_ayer_v3","activo_fisicamente_ayer_v4")]==1, na.rm=TRUE)>0,1,0)
dat$alcohol_ayer<-ifelse(rowSums(dat[,c("alcohol_ayer_v1","alcohol_ayer_v2","alcohol_ayer_v3","alcohol_ayer_v4")]==1, na.rm=TRUE)>0,1,0)
dat$imc_basal<-dat$imc_v1
dat$obes_basal<-dat$obes_v1
dat$obes2_basal<-with(dat,ifelse(obes_v1==3,1,0))
dat$obabd_basal<-dat$obabd_v1
dat$mvltpa_basal<-dat$mvltpa_v1
dat$sedh_basal<-dat$sedentarismo_horas_v1
dat$dietaq_basal<-dat$dietaq
dat<-dat[!is.na(dat$grupo), ]
dat<-dat[,c("id","grupo","mujer","edad","fumador","hipolip_antiinf","suplementos","actfis_ayer","alcohol_ayer",
            "imc_basal","obes_basal","obes2_basal","obabd_basal","mvltpa_basal","sedh_basal","dietaq_basal",
            "pas_v1","pad_v1","pulso_v1","imc_v1","cintura_v1","cadera_v1","whr_v1",
            "tc_v1","tg_v1","hdlc_v1","ldlc_v1","vldlc_v1","nonhdlc_v1","aip_v1","glucosa_v1","insulina_v1","homa_v1",
            "std_wt_v1","lbm_v1","tbw_v1","ecw_v1","icw_v1","mbf_v1","pbf_v1","ratio_v1","bmr_v1","lt_arm_v1","rt_arm_v1","lt_leg_v1","rt_leg_v1","trunk_v1","impedance_v1",
            "tg_iAUC_v1","tg_tmax_v1","tg_cmax_v1","glucosa_dif2h_v1","insulina_dif2h_v1","homa_dif2h_v1",
            "pas_v2","pad_v2","pulso_v2","imc_v2","cintura_v2","cadera_v2","whr_v2",
            "tc_v2","tg_v2","hdlc_v2","ldlc_v2","vldlc_v2","nonhdlc_v2","aip_v2","glucosa_v2","insulina_v2","homa_v2",
            "std_wt_v2","lbm_v2","tbw_v2","ecw_v2","icw_v2","mbf_v2","pbf_v2","ratio_v2","bmr_v2","lt_arm_v2","rt_arm_v2","lt_leg_v2","rt_leg_v2","trunk_v2","impedance_v2",
            "tg_iAUC_v2","tg_tmax_v2","tg_cmax_v2","glucosa_dif2h_v2","insulina_dif2h_v2","homa_dif2h_v2",
            "pas_v3","pad_v3","pulso_v3","imc_v3","cintura_v3","cadera_v3","whr_v3",
            "tc_v3","tg_v3","hdlc_v3","ldlc_v3","vldlc_v3","nonhdlc_v3","aip_v3","glucosa_v3","insulina_v3","homa_v3",
            "std_wt_v3","lbm_v3","tbw_v3","ecw_v3","icw_v3","mbf_v3","pbf_v3","ratio_v3","bmr_v3","lt_arm_v3","rt_arm_v3","lt_leg_v3","rt_leg_v3","trunk_v3","impedance_v3",
            "tg_iAUC_v3","tg_tmax_v3","tg_cmax_v3","glucosa_dif2h_v3","insulina_dif2h_v3","homa_dif2h_v3",
            "pas_v4","pad_v4","pulso_v4","imc_v4","cintura_v4","cadera_v4","whr_v4",
            "tc_v4","tg_v4","hdlc_v4","ldlc_v4","vldlc_v4","nonhdlc_v4","aip_v4","glucosa_v4","insulina_v4","homa_v4",
            "std_wt_v4","lbm_v4","tbw_v4","ecw_v4","icw_v4","mbf_v4","pbf_v4","ratio_v4","bmr_v4","lt_arm_v4","rt_arm_v4","lt_leg_v4","rt_leg_v4","trunk_v4","impedance_v4",
            "tg_iAUC_v4","tg_tmax_v4","tg_cmax_v4","glucosa_dif2h_v4","insulina_dif2h_v4","homa_dif2h_v4")]


# IMPUTACION DE COVARIABLES FALTANTES #

vars_all <- c("id","grupo","mujer","edad","fumador","hipolip_antiinf","suplementos","actfis_ayer","alcohol_ayer",
              "imc_basal","obes_basal","obabd_basal","mvltpa_basal","sedh_basal","dietaq_basal",
              "tg_v1","hdlc_v1","ldlc_v1","pas_v1","glucosa_v1","homa_v1")
targets  <- c("fumador","mvltpa_basal","sedh_basal")
predicts <- setdiff(vars_all, targets)

dat_imp <- dat %>% 
  select(all_of(vars_all)) %>% 
  select(where(~ !all(is.na(.x))))

fill_mode <- function(x) {
  tab <- table(x, useNA = "no")
  if (length(tab) == 0) return(x) # all NA -> leave as is
  rep.int(names(which.max(tab)), length(x))}

predictors_complete <- dat_imp %>% 
  select(all_of(predicts)) %>% 
  mutate(across(where(is.numeric), ~ {
    m <- suppressWarnings(median(.x, na.rm = TRUE))
    if (is.finite(m)) replace(.x, is.na(.x), m) else .x
  })) %>% 
  mutate(across(where(~ is.character(.x) || is.factor(.x)), ~ {
    m <- suppressWarnings(names(which.max(table(.x, useNA = "no"))))
    if (length(m) == 0) .x else replace(.x, is.na(.x), m)
  }))

x_for_mf <- bind_cols(dat_imp[targets], predictors_complete)

set.seed(1988)
mr <- missRanger(
  x_for_mf,
  num.trees   = 300,      # 100–300
  maxiter     = 5,        # usually enough here
  pmm.k       = 3,        # predictive mean matching (stable for numeric)
  sample.fraction = 0.7,  # subsample rows for speed
  respect.unordered.factors = "order",
  verbose     = TRUE
)

dat[targets] <- mr[targets]
dat_imp<-NULL
mr<-NULL
predictors_complete<-NULL
x_for_mf<-NULL

save(dat,file="./Data/rio.RData")


# DATABASE EN FORMATO LONG #

covars <- dat %>%
  select(id,mujer,edad,fumador,hipolip_antiinf,suplementos,actfis_ayer,alcohol_ayer,
         imc_basal,obes_basal,obes2_basal,obabd_basal,mvltpa_basal,sedh_basal,dietaq_basal)

# A=Control, B=Intervencion?
dat_long <- dat %>%
  select(
    -mujer, -edad, -fumador, -hipolip_antiinf, -suplementos,
    -actfis_ayer, -alcohol_ayer,
    -imc_basal, -obes_basal, -obes2_basal, -obabd_basal,
    -mvltpa_basal, -sedh_basal, -dietaq_basal
  ) %>%
  pivot_longer(
    cols = matches("_v[1-4]$"),
    names_to   = c(".value", "visit"),
    names_pattern = "(.*)_v([1-4])"
  ) %>%
  mutate(
    visit  = as.integer(visit),
    period = if_else(visit <= 2, 1L, 2L),
    
    # A = 0, B = 1
    treat = case_when(
      grupo == "AB" & period == 1 ~ 0L,  # periodo 1, grupo AB → A
      grupo == "AB" & period == 2 ~ 1L,  # periodo 2, grupo AB → B
      grupo == "BA" & period == 1 ~ 1L,  # periodo 1, grupo BA → B
      grupo == "BA" & period == 2 ~ 0L,  # periodo 2, grupo BA → A
      TRUE ~ NA_integer_
    ),
    
    treat  = factor(treat, levels = c(0, 1)),  # factor 0/1
    period = factor(period),
    grupo  = factor(grupo)
  ) %>%
  left_join(covars, by = "id")

save(dat_long,file="./Data/rio_long.RData")


############################
### ANALISIS ESTADSTICOS ###
############################

### DESCRIPTIVA ###
###################

rm(list = ls(envir=.GlobalEnv)[sapply(ls(envir=.GlobalEnv),
                                      function(x) inherits(get(x, envir = .GlobalEnv), c("data.frame", "tbl_df")))], envir = .GlobalEnv)
load("./Data/rio.RData")

xxx<-dat[,c("id","grupo","mujer","edad","dietaq_basal","alcohol_ayer","mvltpa_basal","sedh_basal","fumador","hipolip_antiinf","suplementos",
            "obes_basal","obabd_basal","tg_v1","hdlc_v1","ldlc_v1","glucosa_v1","pas_v1")]
xxx$sel<-1

basal2<-NULL
basal2<-createTable(compareGroups(grupo~.
                                  -id-sel,
                                  xxx, method=c("mujer"=3,"alcohol_ayer"=3,"mvltpa_basal"=2,
                                                "fumador"=3,"hipolip_antiinf"=3,"suplementos"=3,
                                                "obes_basal"=3,"obabd_basal"=3)),
                    show.n=TRUE, hide.no=0)

tab2<-NULL
tab2<-createTable(compareGroups(sel~.
                                -id-grupo,
                                xxx, method=c("mujer"=3,"alcohol_ayer"=3,"mvltpa_basal"=2,
                                              "fumador"=3,"hipolip_antiinf"=3,"suplementos"=3,
                                              "obes_basal"=3,"obabd_basal"=3)),
                  show.n=TRUE, hide.no=0)

basal2<-cbind(tab2$descr[,1],basal2$descr)
colnames(basal2)<-c("All (n=40)","AB (n=21)","BA (n=19)","P-value","N")
write.table(basal2,file="./Outputs/descriptive.csv",sep=";",col.names=NA)


### ANALISIS POR MODELOS MIXTOS ###
###################################

rm(list = ls(envir=.GlobalEnv)[sapply(ls(envir=.GlobalEnv),
                                      function(x) inherits(get(x, envir = .GlobalEnv), c("data.frame", "tbl_df")))], envir = .GlobalEnv)
load("./Data/rio_long.RData")

vars01<-c("tg","tc","hdlc","ldlc","vldlc","nonhdlc","tg_iAUC","tg_tmax","tg_cmax",
          "glucosa","insulina","homa","glucosa_dif2h","insulina_dif2h","homa_dif2h",
          "imc","cintura","cadera","whr","pas","pad","pulso",
          "std_wt","lbm","tbw","ecw","icw","mbf","pbf","bmr")

tab<-NULL

for(i in 1:length(vars01))
  
{
  xxx<-dat_long[,c("id",vars01[i],"treat","period","visit","grupo","mujer","edad",
                   "dietaq_basal","alcohol_ayer","mvltpa_basal","sedh_basal","fumador","hipolip_antiinf","suplementos","obes2_basal")]
  xxx<-na.omit(xxx)
  sample<-floor(dim(xxx)[1]/4)
  names(xxx)<-c("id","variable","treat","period","visit","grupo","mujer","edad",
                "dietaq_basal","alcohol_ayer","mvltpa_basal","sedh_basal","fumador","hipolip_antiinf","suplementos","obes2_basal")
  xxx$treat<-factor(xxx$treat, levels = c(0, 1))
  
  xxx <- xxx %>%
    arrange(id, visit) %>%
    group_by(id) %>%
    mutate(
      prev_treat = lag(treat),  # tratamiento (0/1) en la visita previa
      carryover = if_else(
        period == 2 & !is.na(prev_treat),
        as.character(prev_treat),  # "0" o "1" según el tratamiento del periodo 1
        "None"
      )
    ) %>%
    ungroup() %>%
    mutate(
      carryover = factor(carryover, levels = c("None", "0", "1"))
    )
  
  mod01<-lmer(variable ~ treat + period + grupo + (1 | id),
              data = xxx)
  coef01<-beta_se_ic_guapa2(summary(mod01)$coef[2,1],summary(mod01)$coef[2,2])
  beta01<-beta_se_ic_guapa3(summary(mod01)$coef[2,1],summary(mod01)$coef[2,2])[1]
  lo01<-beta_se_ic_guapa3(summary(mod01)$coef[2,1],summary(mod01)$coef[2,2])[2]
  hi01<-beta_se_ic_guapa3(summary(mod01)$coef[2,1],summary(mod01)$coef[2,2])[3]
  pval01<-pval_guapa(summary(mod01)$coef[2,5])

  mod02<-lmer(variable ~ treat + period + grupo + (1 | id) + mujer + edad  
              + dietaq_basal + alcohol_ayer + mvltpa_basal + fumador + suplementos + obes2_basal,
              data = xxx)
  coef02<-beta_se_ic_guapa2(summary(mod02)$coef[2,1],summary(mod02)$coef[2,2])
  beta02<-beta_se_ic_guapa3(summary(mod02)$coef[2,1],summary(mod02)$coef[2,2])[1]
  lo02<-beta_se_ic_guapa3(summary(mod02)$coef[2,1],summary(mod02)$coef[2,2])[2]
  hi02<-beta_se_ic_guapa3(summary(mod02)$coef[2,1],summary(mod02)$coef[2,2])[3]
  pval02<-pval_guapa(summary(mod02)$coef[2,5])
  
  pval_group_effect<-pval_guapa(summary(mod02)$coef[4,5])
  
  mod03<-lmer(variable ~ treat + period + grupo + (1 | id) + carryover + mujer + edad  
              + dietaq_basal + alcohol_ayer + mvltpa_basal + fumador + suplementos + obes2_basal,
              data = xxx)
  pval_carryover<-pval_guapa(as.numeric(anova(mod02, mod03)[2,8]))
  
  xxx_p1 <- xxx %>%
    filter(period == 1)
  mod04<-lm(variable ~ treat + mujer + edad  
              + dietaq_basal + alcohol_ayer + mvltpa_basal + fumador + suplementos + obes2_basal,
              data = xxx_p1)
  coef_period1<-beta_se_ic_guapa2(summary(mod04)$coef[2,1],summary(mod04)$coef[2,2])
  beta_period1<-beta_se_ic_guapa3(summary(mod04)$coef[2,1],summary(mod04)$coef[2,2])[1]
  lo_period1<-beta_se_ic_guapa3(summary(mod04)$coef[2,1],summary(mod04)$coef[2,2])[2]
  hi_period1<-beta_se_ic_guapa3(summary(mod04)$coef[2,1],summary(mod04)$coef[2,2])[3]
  pval_period1<-pval_guapa(summary(mod04)$coef[2,4])
  
  tab<-rbind(tab,cbind(sample,coef01,pval01,coef02,pval02,pval_group_effect,pval_carryover,
                       beta01,lo01,hi01,beta02,lo02,hi02,
                       coef_period1,beta_period1,lo_period1,hi_period1,pval_period1))
}
  
rownames(tab)<-vars01
write.table(tab,file="./Outputs/resultados.csv",sep=";",col.names=NA)


### FOREST PLOTS ###
####################

### DATASETS ###

tab<-read.csv2("./Outputs/resultados.csv",header=TRUE,sep=";",dec=".")
tab <- tab[, !(names(tab) == "" | is.na(names(tab)))]
tab<-as.data.frame(tab)
names(tab)<-c("bmk","sample","coef01","pval01","coef02","pval02","pval_group_effect","pval_carryover",
              "beta01","lo01","hi01","beta02","lo02","hi02","coef_period1","beta_period1","lo_period1","hi_period1","pval_period1")
tab$bmk<-c("01. Triglycerides\n(mg/dL)","02. Total-C\n(mg/dL)","03. HDL-C\n(mg/dL)","04. LDL-C\n(mg/dL)",
           "05. VLDL-C\n(mg/dL)","06. Non-HDL-C\n(mg/dL)",
           "01. Triglycerides\nAUC\n(mg/dL·h)","02. Triglycerides\nmaximum\n(minutes)","03. Triglycerides\nmaximum\n(mg/dL)",
           "01. Glucose\n(mg/dL)","02. Insulin\n(μUI/mL)","03. HOMA-IR\n(units)",
           "04. Glucose\n2h incr.\n(mg/dL·h)","05. Insulin\n2h incr.\n(μUI/mL·h)","06. HOMA\n2h incr.\n(units/h)",
           "01. BMI\n(kg/m2)","02. Waist circ.\n(cm)","03. Hip circ.\n(cm)","04. Waist-to-\nhip ratio","05. SBP\n(mmHg)","06. DBP\n(mmHg)","07. Beats\nper minute",
           "01. Std. weight\n(kg)","02. Lean mass\n(kg)","03. Body water\n(kg)","04. Extracel.\nwater (kg)","05. Intracel.\nwater (kg)",
           "06. Body fat\n(kg)","07. Body fat\n(%)","08. Basal metab.\nrate (kcal)")

tab_lip<-tab[c(1:6),]
forest_lip <- bind_rows(
  tab_lip %>%
    transmute(
      bmk,
      model = "02. Non-adjusted",
      coef  = coef01,
      est   = beta01,
      lo    = lo01,
      hi    = hi01),
  tab_lip %>%
    transmute(
      bmk,
      model = "01. Adjusted",
      coef  = coef02,
      est   = beta02,
      lo    = lo02,
      hi    = hi02)
)

forest_lip$model<-factor(forest_lip$model, levels = c("01. Adjusted","02. Non-adjusted"))
forest_lip <- forest_lip %>%
  mutate(
    est = as.numeric(est),
    lo  = as.numeric(lo),
    hi  = as.numeric(hi)
  ) %>%
  group_by(bmk) %>%
  mutate(y_text = max(hi, na.rm = TRUE) * mult_text) %>%
  ungroup()

tab_kin<-tab[c(7:9),]
forest_kin <- bind_rows(
  tab_kin %>%
    transmute(
      bmk,
      model = "02. Non-adjusted",
      coef  = coef01,
      est   = beta01,
      lo    = lo01,
      hi    = hi01),
  tab_kin %>%
    transmute(
      bmk,
      model = "01. Adjusted",
      coef  = coef02,
      est   = beta02,
      lo    = lo02,
      hi    = hi02)
)

forest_kin$model<-factor(forest_kin$model, levels = c("01. Adjusted","02. Non-adjusted"))
forest_kin <- forest_kin %>%
  mutate(
    est = as.numeric(est),
    lo  = as.numeric(lo),
    hi  = as.numeric(hi)
  ) %>%
  group_by(bmk) %>%
  mutate(y_text = max(hi, na.rm = TRUE) * mult_text) %>%
  ungroup()

tab_gluc<-tab[c(10:15),]
forest_gluc <- bind_rows(
  tab_gluc %>%
    transmute(
      bmk,
      model = "02. Non-adjusted",
      coef  = coef01,
      est   = beta01,
      lo    = lo01,
      hi    = hi01),
  tab_gluc %>%
    transmute(
      bmk,
      model = "01. Adjusted",
      coef  = coef02,
      est   = beta02,
      lo    = lo02,
      hi    = hi02)
)

forest_gluc$model<-factor(forest_gluc$model, levels = c("01. Adjusted","02. Non-adjusted"))
forest_gluc <- forest_gluc %>%
  mutate(
    est = as.numeric(est),
    lo  = as.numeric(lo),
    hi  = as.numeric(hi)
  ) %>%
  group_by(bmk) %>%
  mutate(y_text = max(hi, na.rm = TRUE) * mult_text) %>%
  ungroup()

tab_clin<-tab[c(16:22),]
forest_clin <- bind_rows(
  tab_clin %>%
    transmute(
      bmk,
      model = "02. Non-adjusted",
      coef  = coef01,
      est   = beta01,
      lo    = lo01,
      hi    = hi01),
  tab_clin %>%
    transmute(
      bmk,
      model = "01. Adjusted",
      coef  = coef02,
      est   = beta02,
      lo    = lo02,
      hi    = hi02)
)

forest_clin$model<-factor(forest_clin$model, levels = c("01. Adjusted","02. Non-adjusted"))
forest_clin <- forest_clin %>%
  mutate(
    est = as.numeric(est),
    lo  = as.numeric(lo),
    hi  = as.numeric(hi)
  ) %>%
  group_by(bmk) %>%
  mutate(y_text = max(hi, na.rm = TRUE) * mult_text) %>%
  ungroup()

tab_anthr<-tab[c(16:19),]
forest_anthr <- bind_rows(
  tab_anthr %>%
    transmute(
      bmk,
      model = "02. Non-adjusted",
      coef  = coef01,
      est   = beta01,
      lo    = lo01,
      hi    = hi01),
  tab_anthr %>%
    transmute(
      bmk,
      model = "01. Adjusted",
      coef  = coef02,
      est   = beta02,
      lo    = lo02,
      hi    = hi02)
)

forest_anthr$model<-factor(forest_anthr$model, levels = c("01. Adjusted","02. Non-adjusted"))
forest_anthr <- forest_anthr %>%
  mutate(
    est = as.numeric(est),
    lo  = as.numeric(lo),
    hi  = as.numeric(hi)
  ) %>%
  group_by(bmk) %>%
  mutate(y_text = max(hi, na.rm = TRUE) * mult_text) %>%
  ungroup()

tab_bia<-tab[c(23:29),]
forest_bia <- bind_rows(
  tab_bia %>%
    transmute(
      bmk,
      model = "02. Non-adjusted",
      coef  = coef01,
      est   = beta01,
      lo    = lo01,
      hi    = hi01),
  tab_bia %>%
    transmute(
      bmk,
      model = "01. Adjusted",
      coef  = coef02,
      est   = beta02,
      lo    = lo02,
      hi    = hi02)
)

forest_bia$model<-factor(forest_bia$model, levels = c("01. Adjusted","02. Non-adjusted"))
forest_bia <- forest_bia %>%
  mutate(
    est = as.numeric(est),
    lo  = as.numeric(lo),
    hi  = as.numeric(hi)
  ) %>%
  group_by(bmk) %>%
  mutate(y_text = max(hi, na.rm = TRUE) * mult_text) %>%
  ungroup()


### LIPIDOS ###

mult_text <- 2  # puedes ajustar si el texto se solapa
max_hi <- max(forest_lip$hi, na.rm = TRUE)
figure <- ggplot(data = forest_lip,
                 aes(x = model, y = est, ymin = lo, ymax = hi)) +
  geom_hline(yintercept = 0, linetype = 2) +
  geom_pointrange(aes(col = model), size = 0.7, shape = 15) +
  geom_errorbar(aes(ymin = lo, ymax = hi, col = model), width = 0.6, cex = 1) +
  geom_text(data = forest_lip, size = 4.5, aes(y = max_hi*mult_text, x = model, label = coef, hjust = "inward")) +
  xlab(" ") +
  ylab("Intervention vs. control differences\n(adjusted mean, 95% CI)") +
  facet_wrap(
    ~ bmk,
    strip.position = "left",
    nrow   = length(unique(forest_lip$bmk)),
    scales = "free_y"
  ) +
  coord_flip() +
  theme_minimal() +
  theme(
    legend.position   = "bottom",
    panel.grid.major  = element_blank(),
    panel.grid.minor  = element_blank(),
    panel.background  = element_blank(),
    plot.background   = element_rect(fill = "white", color = NA),
    axis.line         = element_line(colour = "black"),
    axis.text.y       = element_blank(),
    axis.text.x       = element_text(size = 11),
    axis.ticks.y      = element_line(),
    axis.ticks.x      = element_line(),
    axis.title.x      = element_text(size = 13),
    axis.title.y      = element_text(size = 6),
    strip.text        = element_text(size = 5.5)
  )

ggsave("./Outputs/forest_lip.jpg",
       plot   = figure,
       units  = "px",
       width  = 8000,
       height = 6000,
       dpi    = 1200,
       bg     = "transparent",
       device = "jpeg")


### CINETICA ###

mult_text <- 2.75  # puedes ajustar si el texto se solapa
max_hi <- max(forest_kin$hi, na.rm = TRUE)
figure <- ggplot(data = forest_kin,
                 aes(x = model, y = est, ymin = lo, ymax = hi)) +
  geom_hline(yintercept = 0, linetype = 2) +
  geom_pointrange(aes(col = model), size = 0.7, shape = 15) +
  geom_errorbar(aes(ymin = lo, ymax = hi, col = model), width = 0.6, cex = 1) +
  geom_text(data = forest_kin, size = 4.5, aes(y = max_hi*mult_text, x = model, label = coef, hjust = "inward")) +
  xlab(" ") +
  ylab("Intervention vs. control differences\n(adjusted mean, 95% CI)") +
  facet_wrap(
    ~ bmk,
    strip.position = "left",
    nrow   = length(unique(forest_kin$bmk)),
    scales = "free_y"
  ) +
  coord_flip() +
  theme_minimal() +
  theme(
    legend.position   = "bottom",
    panel.grid.major  = element_blank(),
    panel.grid.minor  = element_blank(),
    panel.background  = element_blank(),
    plot.background   = element_rect(fill = "white", color = NA),
    axis.line         = element_line(colour = "black"),
    axis.text.y       = element_blank(),
    axis.text.x       = element_text(size = 11),
    axis.ticks.y      = element_line(),
    axis.ticks.x      = element_line(),
    axis.title.x      = element_text(size = 13),
    axis.title.y      = element_text(size = 6),
    strip.text        = element_text(size = 5.5)
  )

ggsave("./Outputs/forest_kin.jpg",
       plot   = figure,
       units  = "px",
       width  = 8000,
       height = 4000,
       dpi    = 1200,
       bg     = "transparent",
       device = "jpeg")


### GLUCOSA ###

mult_text <- 5  # puedes ajustar si el texto se solapa
max_hi <- max(forest_gluc$hi, na.rm = TRUE)
figure <- ggplot(data = forest_gluc,
                 aes(x = model, y = est, ymin = lo, ymax = hi)) +
  geom_hline(yintercept = 0, linetype = 2) +
  geom_pointrange(aes(col = model), size = 0.7, shape = 15) +
  geom_errorbar(aes(ymin = lo, ymax = hi, col = model), width = 0.6, cex = 1) +
  geom_text(data = forest_gluc, size = 4.5, aes(y = max_hi*mult_text, x = model, label = coef, hjust = "inward")) +
  xlab(" ") +
  ylab("Intervention vs. control differences\n(adjusted mean, 95% CI)") +
  facet_wrap(
    ~ bmk,
    strip.position = "left",
    nrow   = length(unique(forest_gluc$bmk)),
    scales = "free_y"
  ) +
  coord_flip() +
  theme_minimal() +
  theme(
    legend.position   = "bottom",
    panel.grid.major  = element_blank(),
    panel.grid.minor  = element_blank(),
    panel.background  = element_blank(),
    plot.background   = element_rect(fill = "white", color = NA),
    axis.line         = element_line(colour = "black"),
    axis.text.y       = element_blank(),
    axis.text.x       = element_text(size = 11),
    axis.ticks.y      = element_line(),
    axis.ticks.x      = element_line(),
    axis.title.x      = element_text(size = 13),
    axis.title.y      = element_text(size = 6),
    strip.text        = element_text(size = 5.5)
  )

ggsave("./Outputs/forest_gluc.jpg",
       plot   = figure,
       units  = "px",
       width  = 8000,
       height = 6000,
       dpi    = 1200,
       bg     = "transparent",
       device = "jpeg")


### CLINICA ###

mult_text <- 2  # puedes ajustar si el texto se solapa
max_hi <- max(forest_clin$hi, na.rm = TRUE)
figure <- ggplot(data = forest_clin,
                 aes(x = model, y = est, ymin = lo, ymax = hi)) +
  geom_hline(yintercept = 0, linetype = 2) +
  geom_pointrange(aes(col = model), size = 0.7, shape = 15) +
  geom_errorbar(aes(ymin = lo, ymax = hi, col = model), width = 0.6, cex = 1) +
  geom_text(data = forest_clin, size = 4.5, aes(y = max_hi*mult_text, x = model, label = coef, hjust = "inward")) +
  xlab(" ") +
  ylab("Intervention vs. control differences\n(adjusted mean, 95% CI)") +
  facet_wrap(
    ~ bmk,
    strip.position = "left",
    nrow   = length(unique(forest_clin$bmk)),
    scales = "free_y"
  ) +
  coord_flip() +
  theme_minimal() +
  theme(
    legend.position   = "bottom",
    panel.grid.major  = element_blank(),
    panel.grid.minor  = element_blank(),
    panel.background  = element_blank(),
    plot.background   = element_rect(fill = "white", color = NA),
    axis.line         = element_line(colour = "black"),
    axis.text.y       = element_blank(),
    axis.text.x       = element_text(size = 11),
    axis.ticks.y      = element_line(),
    axis.ticks.x      = element_line(),
    axis.title.x      = element_text(size = 13),
    axis.title.y      = element_text(size = 6),
    strip.text        = element_text(size = 5.5)
  )

ggsave("./Outputs/forest_clin.jpg",
       plot   = figure,
       units  = "px",
       width  = 8000,
       height = 6000,
       dpi    = 1200,
       bg     = "transparent",
       device = "jpeg")


### ANTROPOMETRIA ###

mult_text <- 2  # puedes ajustar si el texto se solapa
max_hi <- max(forest_anthr$hi, na.rm = TRUE)
figure <- ggplot(data = forest_anthr,
                 aes(x = model, y = est, ymin = lo, ymax = hi)) +
  geom_hline(yintercept = 0, linetype = 2) +
  geom_pointrange(aes(col = model), size = 0.7, shape = 15) +
  geom_errorbar(aes(ymin = lo, ymax = hi, col = model), width = 0.6, cex = 1) +
  geom_text(data = forest_anthr, size = 4.5, aes(y = max_hi*mult_text, x = model, label = coef, hjust = "inward")) +
  xlab(" ") +
  ylab("Intervention vs. control differences\n(adjusted mean, 95% CI)") +
  facet_wrap(
    ~ bmk,
    strip.position = "left",
    nrow   = length(unique(forest_anthr$bmk)),
    scales = "free_y"
  ) +
  coord_flip() +
  theme_minimal() +
  theme(
    legend.position   = "bottom",
    panel.grid.major  = element_blank(),
    panel.grid.minor  = element_blank(),
    panel.background  = element_blank(),
    plot.background   = element_rect(fill = "white", color = NA),
    axis.line         = element_line(colour = "black"),
    axis.text.y       = element_blank(),
    axis.text.x       = element_text(size = 11),
    axis.ticks.y      = element_line(),
    axis.ticks.x      = element_line(),
    axis.title.x      = element_text(size = 13),
    axis.title.y      = element_text(size = 6),
    strip.text        = element_text(size = 5.5)
  )

ggsave("./Outputs/forest_anthr.jpg",
       plot   = figure,
       units  = "px",
       width  = 8000,
       height = 4500,
       dpi    = 1200,
       bg     = "transparent",
       device = "jpeg")


### BIOIMPEDANCIA ###

mult_text <- 2  # puedes ajustar si el texto se solapa
max_hi <- max(forest_bia$hi, na.rm = TRUE)
figure <- ggplot(data = forest_bia,
                 aes(x = model, y = est, ymin = lo, ymax = hi)) +
  geom_hline(yintercept = 0, linetype = 2) +
  geom_pointrange(aes(col = model), size = 0.7, shape = 15) +
  geom_errorbar(aes(ymin = lo, ymax = hi, col = model), width = 0.6, cex = 1) +
  geom_text(data = forest_bia, size = 4.5, aes(y = max_hi*mult_text, x = model, label = coef, hjust = "inward")) +
  xlab(" ") +
  ylab("Intervention vs. control differences\n(adjusted mean, 95% CI)") +
  facet_wrap(
    ~ bmk,
    strip.position = "left",
    nrow   = length(unique(forest_bia$bmk)),
    scales = "free_y"
  ) +
  coord_flip() +
  theme_minimal() +
  theme(
    legend.position   = "bottom",
    panel.grid.major  = element_blank(),
    panel.grid.minor  = element_blank(),
    panel.background  = element_blank(),
    plot.background   = element_rect(fill = "white", color = NA),
    axis.line         = element_line(colour = "black"),
    axis.text.y       = element_blank(),
    axis.text.x       = element_text(size = 11),
    axis.ticks.y      = element_line(),
    axis.ticks.x      = element_line(),
    axis.title.x      = element_text(size = 13),
    axis.title.y      = element_text(size = 6),
    strip.text        = element_text(size = 5.5)
  )

ggsave("./Outputs/forest_bia.jpg",
       plot   = figure,
       units  = "px",
       width  = 8000,
       height = 6500,
       dpi    = 1200,
       bg     = "transparent",
       device = "jpeg")




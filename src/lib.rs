use rand::{distributions::Uniform, Rng};
use std::fmt::{Debug, Display, Formatter, Result};
use std::str::FromStr;
use thiserror::Error;
use anyhow;

#[derive(Error, Debug)]
pub enum CPFError {
    #[error("Dígito verificador inválido.")]
    DigitoVerificadorInvalido,
    #[error("Tamanho do CPF inválido.")]
    TamanhoInvalido,
    #[error("O dígito referente à Região Fiscal não existe.")]
    SemDigitoDaRegiaoFiscal,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum RegiaoFiscal {
    RF01,
    RF02,
    RF03,
    RF04,
    RF05,
    RF06,
    RF07,
    RF08,
    RF09,
    RF10
}

impl Debug for RegiaoFiscal {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match *self {
            RegiaoFiscal::RF01 => write!(f, "1ª Região Fiscal (DF, GO, TO, MT e MS)"),
            RegiaoFiscal::RF02 => write!(f, "2ª Região Fiscal (AC, AM, AP, PA, RO e RR)"),
            RegiaoFiscal::RF03 => write!(f, "3ª Região Fiscal (CE, MA e PI.)"),
            RegiaoFiscal::RF04 => write!(f, "4ª Região Fiscal (AL, PB, PE e RN)"),
            RegiaoFiscal::RF05 => write!(f, "5ª Região Fiscal (BA e SE)"),
            RegiaoFiscal::RF06 => write!(f, "6ª Região Fiscal (MG)"),
            RegiaoFiscal::RF07 => write!(f, "7ª Região Fiscal (ES e RJ)"),
            RegiaoFiscal::RF08 => write!(f, "8ª Região Fiscal (SP)"),
            RegiaoFiscal::RF09 => write!(f, "9ª Região Fiscal (PR e SC)"),
            RegiaoFiscal::RF10 => write!(f, "10ª Região Fiscal (RS)"),
        }
    }
}

fn get_digito_verificador(digitos: &Vec<u8>) -> anyhow::Result<u8, CPFError> {

    if digitos.len() != 9 && digitos.len() != 10 {
        return Err(CPFError::TamanhoInvalido);
    }

    let mult_vec: Vec<u8> = (2..=digitos.len() as u8 + 1).collect::<Vec<u8>>().into_iter().rev().collect();
    let result = digitos.iter().zip(mult_vec.iter()).map(|(x, y)| (x * y) as usize).sum::<usize>();
    match (result*10) % 11 {
        remainder if remainder == 10 => Ok(0 as u8),
        remainder => Ok(remainder as u8),
    }
}

fn get_regiao_fiscal(digitos: &Vec<u8>) -> anyhow::Result<RegiaoFiscal, CPFError> {
    match digitos.get(8) {
        Some(1) => Ok(RegiaoFiscal::RF01),
        Some(2) => Ok(RegiaoFiscal::RF02),
        Some(3) => Ok(RegiaoFiscal::RF03),
        Some(4) => Ok(RegiaoFiscal::RF04),
        Some(5) => Ok(RegiaoFiscal::RF05),
        Some(6) => Ok(RegiaoFiscal::RF06),
        Some(7) => Ok(RegiaoFiscal::RF07),
        Some(8) => Ok(RegiaoFiscal::RF08),
        Some(9) => Ok(RegiaoFiscal::RF09),
        Some(0) => Ok(RegiaoFiscal::RF10),
        _ => Err(CPFError::SemDigitoDaRegiaoFiscal)
    }
}

pub fn parse<T: AsRef<str>>(cpf: T) -> anyhow::Result<CPF, CPFError> {
    let digitos: Vec<u8> = cpf.as_ref().chars().filter_map(|c| c.to_digit(10).map(|d| d as u8)).collect::<Vec<u8>>();
    
    if digitos.len() != 11 {
        return Err(CPFError::TamanhoInvalido);
    } else if get_digito_verificador(&digitos[0..9].to_vec())? != digitos[9] || get_digito_verificador(&digitos[0..10].to_vec())? != digitos[10] {
        return Err(CPFError::DigitoVerificadorInvalido);
    }

    let regiao_fiscal: RegiaoFiscal = get_regiao_fiscal(&digitos)?;

    Ok(CPF {digitos, regiao_fiscal})
}

pub fn valid<T>(cpf: T) -> bool 
    where T: AsRef<str> {
    parse(cpf).is_ok()
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CPF {
    digitos: Vec<u8>,
    regiao_fiscal: RegiaoFiscal
}

impl CPF {
    pub fn generate() -> anyhow::Result<Self, CPFError> {

        let mut rng = rand::thread_rng();
        let range = Uniform::new_inclusive(0, 9);
        
        // Obtém os 9 (nove) primeiros dígitos
        let mut digitos: Vec<u8> = (0..9).map(|_| rng.sample(&range)).collect();

        // Obtém o primeiro dígito verificador
        let dv1: u8 = get_digito_verificador(&digitos)?;
        digitos.push(dv1);

        // Obtém o segundo dígito verificador
        let dv2: u8 = get_digito_verificador(&digitos)?;
        digitos.push(dv2);

        let regiao_fiscal = get_regiao_fiscal(&digitos)?;

        Ok(Self {
            digitos,
            regiao_fiscal
        })
    }

    pub fn generate_for_regiao_fiscal(regiao_fiscal: RegiaoFiscal) -> anyhow::Result<Self, CPFError> {

        let mut rng = rand::thread_rng();
        let range = Uniform::new_inclusive(0, 9);

        // Obtém os 8 (oito) primeiros dígitos
        let mut digitos: Vec<u8> = (0..8).map(|_| rng.sample(&range)).collect();

        match regiao_fiscal {
            RegiaoFiscal::RF01 => digitos.push(1),
            RegiaoFiscal::RF02 => digitos.push(2),
            RegiaoFiscal::RF03 => digitos.push(3),
            RegiaoFiscal::RF04 => digitos.push(4),
            RegiaoFiscal::RF05 => digitos.push(5),
            RegiaoFiscal::RF06 => digitos.push(6),
            RegiaoFiscal::RF07 => digitos.push(7),
            RegiaoFiscal::RF08 => digitos.push(8),
            RegiaoFiscal::RF09 => digitos.push(9),
            RegiaoFiscal::RF10 => digitos.push(10),
        }

        // Obtém o primeiro dígito verificador
        let dv1: u8 = get_digito_verificador(&digitos)?;
        digitos.push(dv1);

        // Obtém o segundo dígito verificador
        let dv2: u8 = get_digito_verificador(&digitos)?;
        digitos.push(dv2);

       Ok(Self {
            digitos,
            regiao_fiscal
        })

    }

    pub fn as_str(&self) -> &str {
        self.digitos.iter().map(|s| s.to_string()).collect::<String>().leak()
    }

}

impl Display for CPF {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let digits = self.as_str();
        write!(
            f,
            "{}.{}.{}-{}",
            &digits[0..3],
            &digits[3..6],
            &digits[6..9],
            &digits[9..11]
        )
    }
}

impl FromStr for CPF {
    type Err = CPFError;

    fn from_str(s: &str) -> anyhow::Result<Self, CPFError> {
        parse(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generate_valid_cpf() {
        let cpf = CPF::generate().unwrap();
        assert!(valid(cpf.as_str()));
    }

    #[test]
    fn generate_valid_cpf_for_regiao_fiscal() {
        let cpf = CPF::generate_for_regiao_fiscal(RegiaoFiscal::RF01).unwrap();
        assert_eq!(cpf.regiao_fiscal, RegiaoFiscal::RF01);
    }
}
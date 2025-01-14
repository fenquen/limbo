use chrono::{
    DateTime, Datelike, NaiveDate, NaiveDateTime, NaiveTime, TimeDelta, TimeZone, Timelike, Utc,
};
use std::rc::Rc;

use crate::types::OwnedValue;
use crate::LimboError::InvalidModifier;
use crate::Result;

/// Implementation of the date() SQL function.
pub fn exec_date(values: &[OwnedValue]) -> OwnedValue {
    let maybe_dt = match values.first() {
        None => parse_naive_date_time(&OwnedValue::Text(Rc::new("now".to_string()))),
        Some(value) => parse_naive_date_time(value),
    };
    // early return, no need to look at modifiers if result invalid
    if maybe_dt.is_none() {
        return OwnedValue::Text(Rc::new(String::new()));
    }

    // apply modifiers if result is valid
    let mut dt = maybe_dt.unwrap();
    for modifier in values.iter().skip(1) {
        if let OwnedValue::Text(modifier_str) = modifier {
            if apply_modifier(&mut dt, modifier_str).is_err() {
                return OwnedValue::Text(Rc::new(String::new()));
            }
        } else {
            return OwnedValue::Text(Rc::new(String::new()));
        }
    }

    OwnedValue::Text(Rc::new(get_date_from_naive_datetime(dt)))
}

/// Implementation of the time() SQL function.
pub fn exec_time(time_value: &[OwnedValue]) -> OwnedValue {
    let maybe_dt = match time_value.first() {
        None => parse_naive_date_time(&OwnedValue::Text(Rc::new("now".to_string()))),
        Some(value) => parse_naive_date_time(value),
    };
    // early return, no need to look at modifiers if result invalid
    if maybe_dt.is_none() {
        return OwnedValue::Text(Rc::new(String::new()));
    }

    // apply modifiers if result is valid
    let mut dt = maybe_dt.unwrap();
    for modifier in time_value.iter().skip(1) {
        if let OwnedValue::Text(modifier_str) = modifier {
            if apply_modifier(&mut dt, modifier_str).is_err() {
                return OwnedValue::Text(Rc::new(String::new()));
            }
        } else {
            return OwnedValue::Text(Rc::new(String::new()));
        }
    }

    OwnedValue::Text(Rc::new(get_time_from_naive_datetime(dt)))
}

fn apply_modifier(dt: &mut NaiveDateTime, modifier: &str) -> Result<()> {
    let parsed_modifier = parse_modifier(modifier)?;

    match parsed_modifier {
        Modifier::Days(days) => *dt += TimeDelta::days(days),
        Modifier::Hours(hours) => *dt += TimeDelta::hours(hours),
        Modifier::Minutes(minutes) => *dt += TimeDelta::minutes(minutes),
        Modifier::Seconds(seconds) => *dt += TimeDelta::seconds(seconds),
        Modifier::TimeOffset(offset) => *dt += offset,
        Modifier::DateOffset { years, months, days } => {
            *dt = dt.checked_add_months(chrono::Months::new((years * 12 + months) as u32)).ok_or_else(|| InvalidModifier("Invalid date offset".to_string()))?;
            *dt += TimeDelta::days(days as i64);
        }
        Modifier::StartOfYear => *dt = NaiveDate::from_ymd_opt(dt.year(), 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap(),
        Modifier::StartOfDay => *dt = dt.date().and_hms_opt(0, 0, 0).unwrap(),
        Modifier::Localtime => {
            let utc_dt = DateTime::<Utc>::from_naive_utc_and_offset(*dt, Utc);
            *dt = utc_dt.with_timezone(&chrono::Local).naive_local();
        }
        Modifier::Utc => {
            let local_dt = chrono::Local.from_local_datetime(dt).unwrap();
            *dt = local_dt.with_timezone(&Utc).naive_utc();
        }
        _ => todo!(),
    }

    Ok(())
}

pub fn exec_unixepoch(time_value: &OwnedValue) -> Result<String> {
    let dt = parse_naive_date_time(time_value);
    match dt {
        Some(dt) => Ok(get_unixepoch_from_naive_datetime(dt)),
        None => Ok(String::new()),
    }
}

fn get_unixepoch_from_naive_datetime(value: NaiveDateTime) -> String {
    value.and_utc().timestamp().to_string()
}

fn parse_naive_date_time(time_value: &OwnedValue) -> Option<NaiveDateTime> {
    match time_value {
        OwnedValue::Text(s) => get_date_time_from_time_value_string(s),
        OwnedValue::Integer(i) => get_date_time_from_time_value_integer(*i),
        OwnedValue::Float(f) => get_date_time_from_time_value_float(*f),
        _ => None,
    }
}

fn get_date_time_from_time_value_string(value: &str) -> Option<NaiveDateTime> {
    // Time-value formats:
    // 1-7. YYYY-MM-DD[THH:MM[:SS[.SSS]]]
    // 8-10. HH:MM[:SS[.SSS]]
    // 11. 'now'
    // 12. DDDDDDDDDD (Julian day number as integer or float)
    //
    // Ref: https://sqlite.org/lang_datefunc.html#tmval

    // Check for 'now'
    if value.trim().eq_ignore_ascii_case("now") {
        return Some(chrono::Local::now().to_utc().naive_utc());
    }

    // Check for Julian day number (integer or float)
    if let Ok(julian_day) = value.parse::<f64>() {
        return get_date_time_from_time_value_float(julian_day);
    }

    // Attempt to parse with various formats
    let date_only_format = "%Y-%m-%d";
    let datetime_formats: [&str; 9] = [
        "%Y-%m-%d %H:%M",
        "%Y-%m-%d %H:%M:%S",
        "%Y-%m-%d %H:%M:%S%.f",
        "%Y-%m-%dT%H:%M",
        "%Y-%m-%dT%H:%M:%S",
        "%Y-%m-%dT%H:%M:%S%.f",
        "%H:%M",
        "%H:%M:%S",
        "%H:%M:%S%.f",
    ];

    // First, try to parse as date-only format
    if let Ok(date) = NaiveDate::parse_from_str(value, date_only_format) {
        return Some(date.and_time(NaiveTime::from_hms_opt(0, 0, 0).unwrap()));
    }

    for format in &datetime_formats {
        if let Some(dt) = if format.starts_with("%H") {
            // For time-only formats, assume date 2000-01-01
            // Ref: https://sqlite.org/lang_datefunc.html#tmval
            parse_datetime_with_optional_tz(&format!("2000-01-01 {}", value), &format!("%Y-%m-%d {}", format))
        } else {
            parse_datetime_with_optional_tz(value, format)
        } {
            return Some(dt);
        }
    }
    None
}

fn parse_datetime_with_optional_tz(value: &str, format: &str) -> Option<NaiveDateTime> {
    // Try parsing with timezone
    let with_tz_format = format.to_owned() + "%:z";
    if let Ok(dt) = DateTime::parse_from_str(value, &with_tz_format) {
        return Some(dt.with_timezone(&Utc).naive_utc());
    }

    let mut value_without_tz = value;
    if value.ends_with('Z') {
        value_without_tz = &value[0..value.len() - 1];
    }

    // Parse without timezone
    if let Ok(dt) = NaiveDateTime::parse_from_str(value_without_tz, format) {
        return Some(dt);
    }
    None
}

fn get_date_time_from_time_value_integer(value: i64) -> Option<NaiveDateTime> {
    i32::try_from(value).map_or_else(
        |_| None,
        |value| get_date_time_from_time_value_float(value as f64),
    )
}

fn get_date_time_from_time_value_float(value: f64) -> Option<NaiveDateTime> {
    if value.is_infinite() || value.is_nan() || !(0.0..5373484.5).contains(&value) {
        return None;
    }
    match julian_day_converter::julian_day_to_datetime(value) {
        Ok(dt) => Some(dt),
        Err(_) => None,
    }
}

fn is_leap_second(dt: &NaiveDateTime) -> bool {
    // The range from 1,000,000,000 to 1,999,999,999 represents the leap second.
    dt.nanosecond() >= 1_000_000_000 && dt.nanosecond() <= 1_999_999_999
}

fn get_date_from_naive_datetime(value: NaiveDateTime) -> String {
    // NaiveDateTime supports leap seconds, but SQLite does not.
    // So we ignore them.
    if is_leap_second(&value) || value > get_max_datetime_exclusive() {
        return String::new();
    }
    value.format("%Y-%m-%d").to_string()
}

fn get_time_from_naive_datetime(value: NaiveDateTime) -> String {
    // NaiveDateTime supports leap seconds, but SQLite does not.
    // So we ignore them.
    if is_leap_second(&value) || value > get_max_datetime_exclusive() {
        return String::new();
    }
    value.format("%H:%M:%S").to_string()
}

fn get_max_datetime_exclusive() -> NaiveDateTime {
    // The maximum date in SQLite is 9999-12-31
    NaiveDateTime::new(
        NaiveDate::from_ymd_opt(10000, 1, 1).unwrap(),
        NaiveTime::from_hms_milli_opt(00, 00, 00, 000).unwrap(),
    )
}

/// Modifier doc https://www.sqlite.org/lang_datefunc.html#modifiers
#[allow(dead_code)]
#[derive(Debug, PartialEq)]
enum Modifier {
    Days(i64),
    Hours(i64),
    Minutes(i64),
    Seconds(i64),
    Months(i32),
    Years(i32),
    TimeOffset(TimeDelta),
    DateOffset {
        years: i32,
        months: i32,
        days: i32,
    },
    DateTimeOffset {
        date: NaiveDate,
        time: Option<NaiveTime>,
    },
    Ceiling,
    Floor,
    StartOfMonth,
    StartOfYear,
    StartOfDay,
    Weekday(u32),
    UnixEpoch,
    JulianDay,
    Auto,
    Localtime,
    Utc,
    Subsec,
}

fn parse_modifier_number(s: &str) -> Result<i64> {
    s.trim()
        .parse::<i64>()
        .map_err(|_| InvalidModifier(format!("Invalid number: {}", s)))
}

/// supports YYYY-MM-DD format for time shift modifiers
fn parse_modifier_date(s: &str) -> Result<NaiveDate> {
    NaiveDate::parse_from_str(s, "%Y-%m-%d")
        .map_err(|_| InvalidModifier("Invalid date format".to_string()))
}

/// supports following formats for time shift modifiers
/// - HH:MM
/// - HH:MM:SS
/// - HH:MM:SS.SSS
fn parse_modifier_time(s: &str) -> Result<NaiveTime> {
    match s.len() {
        5 => NaiveTime::parse_from_str(s, "%H:%M"),
        8 => NaiveTime::parse_from_str(s, "%H:%M:%S"),
        12 => NaiveTime::parse_from_str(s, "%H:%M:%S.%3f"),
        _ => return Err(InvalidModifier(format!("Invalid time format: {}", s))),
    }
        .map_err(|_| InvalidModifier(format!("Invalid time format: {}", s)))
}

fn parse_modifier(modifier: &str) -> Result<Modifier> {
    let modifier = modifier.trim().to_lowercase();

    match modifier.as_str() {
        s if s.ends_with(" days") => Ok(Modifier::Days(parse_modifier_number(&s[..s.len() - 5])?)),
        s if s.ends_with(" hours") => Ok(Modifier::Hours(parse_modifier_number(&s[..s.len() - 6])?)),
        s if s.ends_with(" minutes") => Ok(Modifier::Minutes(parse_modifier_number(&s[..s.len() - 8])?)),
        s if s.ends_with(" seconds") => Ok(Modifier::Seconds(parse_modifier_number(&s[..s.len() - 8])?)),
        s if s.ends_with(" months") => Ok(Modifier::Months(parse_modifier_number(&s[..s.len() - 7])? as i32)),
        s if s.ends_with(" years") => Ok(Modifier::Years(parse_modifier_number(&s[..s.len() - 6])? as i32)),
        s if s.starts_with('+') || s.starts_with('-') => {
            // Parse as DateOffset or DateTimeOffset
            let parts: Vec<&str> = s[1..].split(' ').collect();
            match parts.len() {
                1 => {
                    // first part can be either date ±YYYY-MM-DD or 3 types of time modifiers
                    let date = parse_modifier_date(parts[0]);
                    if let Ok(date) = date {
                        Ok(Modifier::DateTimeOffset { date, time: None })
                    } else {
                        // try to parse time if error parsing date
                        let time = parse_modifier_time(parts[0])?;
                        // TODO handle nanoseconds
                        let time_delta = if s.starts_with('-') {
                            TimeDelta::seconds(-(time.num_seconds_from_midnight() as i64))
                        } else {
                            TimeDelta::seconds(time.num_seconds_from_midnight() as i64)
                        };
                        Ok(Modifier::TimeOffset(time_delta))
                    }
                }
                2 => {
                    let date = parse_modifier_date(parts[0])?;
                    let time = parse_modifier_time(parts[1])?;
                    Ok(Modifier::DateTimeOffset {
                        date,
                        time: Some(time),
                    })
                }
                _ => Err(InvalidModifier("Invalid date/time offset format".to_string())),
            }
        }
        "ceiling" => Ok(Modifier::Ceiling),
        "floor" => Ok(Modifier::Floor),
        "start of month" => Ok(Modifier::StartOfMonth),
        "start of year" => Ok(Modifier::StartOfYear),
        "start of day" => Ok(Modifier::StartOfDay),
        s if s.starts_with("weekday ") => {
            let day = parse_modifier_number(&s[8..])?;
            if !(0..=6).contains(&day) {
                Err(InvalidModifier(
                    "Weekday must be between 0 and 6".to_string(),
                ))
            } else {
                Ok(Modifier::Weekday(day as u32))
            }
        }
        "unixepoch" => Ok(Modifier::UnixEpoch),
        "julianday" => Ok(Modifier::JulianDay),
        "auto" => Ok(Modifier::Auto),
        "localtime" => Ok(Modifier::Localtime),
        "utc" => Ok(Modifier::Utc),
        "subsec" | "subsecond" => Ok(Modifier::Subsec),
        _ => Err(InvalidModifier(format!("Unknown modifier: {}", modifier))),
    }
}
